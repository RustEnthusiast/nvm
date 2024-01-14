use crate::{parser::Item, OptLevel, OutputFileType};
use core::num::ParseIntError;
use grim::{Bits, Endianness};
use inkwell::{
    builder::BuilderError,
    context::Context,
    targets::{CodeModel, FileType, RelocMode, Target, TargetTriple},
    values::BasicMetadataValueEnum,
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
        let nvm = grim::assemble(filename, &asm, Bits::BitNative, Endianness::Native, 4)?;
        std::fs::write(path.with_extension("nvm"), &nvm)?;
    } else {
        let context = Context::create();
        let builder = context.create_builder();
        let module = context.create_module(module_name);

        let fn_type = context.void_type().fn_type(&[], false);
        let function = module.add_function("_start", fn_type, None);
        let basic_block = context.append_basic_block(function, "entry");
        builder.position_at_end(basic_block);
        let asm_fn = context.void_type().fn_type(
            &[context.i64_type().into(), context.i64_type().into()],
            false,
        );
        let asm = context.create_inline_asm(
            asm_fn,
            include_str!("../rt/x86_64-linux.asm").to_string(),
            "{rax},{rdi}".to_string(),
            true,
            false,
            #[cfg(not(any(feature = "llvm4-0", feature = "llvm5-0", feature = "llvm6-0")))]
            None,
            #[cfg(not(any(
                feature = "llvm4-0",
                feature = "llvm5-0",
                feature = "llvm6-0",
                feature = "llvm7-0",
                feature = "llvm8-0",
                feature = "llvm9-0",
                feature = "llvm10-0",
                feature = "llvm11-0",
                feature = "llvm12-0"
            )))]
            false,
        );
        let params: &[BasicMetadataValueEnum] = &[
            context.i64_type().const_int(60, false).into(),
            context.i64_type().const_int(69, false).into(),
        ];
        #[cfg(any(
            feature = "llvm4-0",
            feature = "llvm5-0",
            feature = "llvm6-0",
            feature = "llvm7-0",
            feature = "llvm8-0",
            feature = "llvm9-0",
            feature = "llvm10-0",
            feature = "llvm11-0",
            feature = "llvm12-0",
            feature = "llvm13-0",
            feature = "llvm14-0"
        ))]
        {
            use inkwell::values::CallableValue;
            let callable_value = CallableValue::try_from(asm).unwrap();
            builder.build_call(callable_value, params, "exit").unwrap();
        }
        #[cfg(any(feature = "llvm15-0", feature = "llvm16-0", feature = "llvm17-0"))]
        builder
            .build_indirect_call(asm_fn, asm, params, "exit")
            .unwrap();
        builder.build_return(None)?;
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
        let cpu = match target {
            "x86_64-linux" => Some("x86-64"),
            _ => None,
        };

        let machine = Target::from_triple(&triple)
            .map_err(|_| CodegenError::TargetNonexistent(target.into()))?
            .create_target_machine(
                &triple,
                cpu.as_ref().map_or("", |i| i),
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
            cmd.status()?;
            std::fs::remove_file(&module_path)?;
        }
    }
    Ok(())
}
