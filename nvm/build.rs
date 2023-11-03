use build_const::ConstWriter;
use std::io::Result;

/// The minimum number of registers the virtual machine should have.
const BUILTIN_REGS: usize = 3;

/// Main entry point of the build script.
fn main() -> Result<()> {
    let mut consts = ConstWriter::for_build("constants")?.finish_dependencies();
    consts.add_value("BUILTIN_REGS", "usize", BUILTIN_REGS);
    #[cfg(feature = "bin")]
    {
        let mut bin_consts = ConstWriter::for_build("bin_constants")?.finish_dependencies();
        let reg_count = option_env!("NVM_REG_COUNT")
            .map(|v| {
                v.parse::<usize>()
                    .expect("`NVM_REG_COUNT` should be a `usize` value")
            })
            .unwrap_or(4);
        bin_consts.add_value("REG_COUNT", "usize", BUILTIN_REGS + reg_count);
        let stack_size = option_env!("NVM_STACK_SIZE")
            .map(|v| {
                v.parse::<usize>()
                    .expect("`NVM_STACK_SIZE` should be a `usize` value")
            })
            .unwrap_or((u8::MAX as usize).saturating_add(1));
        bin_consts.add_value("STACK_SIZE", "usize", stack_size);
    }
    Ok(())
}
