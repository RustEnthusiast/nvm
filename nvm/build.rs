use std::io::Result;

/// Main entry point of the build script.
fn main() -> Result<()> {
    #[cfg(feature = "build_const")]
    {
        use build_const::ConstWriter;
        let mut consts = ConstWriter::for_build("constants")?.finish_dependencies();
        let stack_size = option_env!("NVM_STACK_SIZE")
            .map(|v| {
                v.parse::<usize>()
                    .expect("`NVM_STACK_SIZE` should be a `usize` value")
            })
            .unwrap_or((u8::MAX as usize).saturating_add(1));
        consts.add_value("STACK_SIZE", "usize", stack_size);
    }
    Ok(())
}
