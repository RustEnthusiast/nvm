use crate::{parser::Item, OptLevel, OutputFileType};
use core::num::ParseIntError;
use inkwell::{
    builder::BuilderError,
    context::Context,
    targets::{CodeModel, FileType, RelocMode, Target, TargetTriple},
    OptimizationLevel,
};
use std::{
    env::consts::EXE_SUFFIX,
    io::{Error as IOError, ErrorKind},
    path::Path,
    process::Command,
};
use thiserror::Error;

/// Describes a code generation error.
#[derive(Debug, Error)]
pub(super) enum CodegenError {
    /// An LLVM builder error occurred.
    #[error(transparent)]
    BuilderError(#[from] BuilderError),
    /// The LLVM target `target` does not exist.
    #[error("the llvm target {0} does not exist")]
    TargetNonexistent(String),
    /// Parsing an integer during assembly failed.
    #[error(transparent)]
    ParseIntError(#[from] ParseIntError),
    /// An I/O error occurred.
    #[error(transparent)]
    IOError(#[from] IOError),
}

/// Generates code for the given target.
pub(super) fn gen<'src, I: IntoIterator<Item = Item<'src>>>(
    filename: &str,
    target: &str,
    linker: &str,
    out_file_type: OutputFileType,
    opt_level: OptLevel,
    items: I,
) -> Result<(), CodegenError> {
    let path = Path::new(filename);
    let module_name = path
        .file_stem()
        .expect("file stem should be present")
        .to_str()
        .expect("file stem should be valid UTF-8");
    if target == "nvm" {
        let mut asm = String::from(include_str!("../rt/nvm.asm"));
        for item in items {
            match item {
                Item::Fn(f) => asm.push_str(&format!("{} return\n", f.name())),
            }
        }
        let nvm = grim::assemble(filename, &asm)?;
        std::fs::write(path.with_extension("nvm"), &nvm)?;
    } else {
        let context = Context::create();
        let builder = context.create_builder();
        let module = context.create_module(module_name);

        let target_info = match target {
            "x86_64-linux" => {
                let rt_path = path.with_file_name("rt.o");
                Command::new("nasm")
                    .args(["-felf64", "-o"])
                    .arg(&rt_path)
                    .arg("rt/x86_64-linux.asm")
                    .status()?;
                Some(("x86-64", rt_path))
            }
            _ => None,
        };

        for item in items {
            match item {
                Item::Fn(f) => {
                    let fn_type = context.void_type().fn_type(&[], false);
                    let function = module.add_function(f.name(), fn_type, None);
                    let basic_block = context.append_basic_block(function, "entry");
                    builder.position_at_end(basic_block);
                    builder.build_return(None)?;
                }
            }
        }

        Target::initialize_all(&Default::default());
        let triple = TargetTriple::create(target);
        let opt_level = match opt_level {
            OptLevel::None => OptimizationLevel::None,
            OptLevel::Less => OptimizationLevel::Less,
            OptLevel::Default => OptimizationLevel::Default,
            OptLevel::Aggressive => OptimizationLevel::Aggressive,
        };
        let machine = Target::from_triple(&triple)
            .map_err(|_| CodegenError::TargetNonexistent(target.into()))?
            .create_target_machine(
                &triple,
                target_info.as_ref().map_or("", |i| i.0),
                "",
                opt_level,
                RelocMode::Default,
                CodeModel::Default,
            )
            .ok_or(CodegenError::TargetNonexistent(target.into()))?;
        let module_path = match out_file_type {
            OutputFileType::Asm => path.with_extension("asm"),
            _ => path.with_extension("o"),
        };
        let exe_name = path.with_file_name(format!("{module_name}{EXE_SUFFIX}"));

        let file_type = match out_file_type {
            OutputFileType::Asm => FileType::Assembly,
            _ => FileType::Object,
        };
        machine
            .write_to_file(&module, file_type, &module_path)
            .map_err(|e| IOError::new(ErrorKind::Other, e.to_string()))?;
        if out_file_type == OutputFileType::Bin {
            let mut cmd = Command::new(linker);
            cmd.arg("-o");
            cmd.args([&exe_name, &module_path]);
            if let Some((_, rt)) = &target_info {
                cmd.arg(rt);
            }
            cmd.status()?;
            std::fs::remove_file(&module_path)?;
        }
        if let Some((_, rt)) = &target_info {
            std::fs::remove_file(rt)?;
        }
    }
    Ok(())
}
