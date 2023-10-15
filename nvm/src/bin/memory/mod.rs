//! The virtual memory driver.
use build_const::build_const;
use bytemuck::NoUninit;
use nvm::{opcode::OpCode, MemoryDriver, NvmError, UInt};
use std::ptr::addr_of;
build_const!("constants");

/// The virtual memory driver.
pub struct Memory {
    /// The buffer of memory to use as virtual machine RAM.
    buffer: [u8; STACK_SIZE],
}
impl Memory {
    /// Creates a new memory driver using `buffer` as a virtual memory buffer.
    #[inline]
    pub const fn new() -> Self {
        Self {
            buffer: [OpCode::Exit as _; STACK_SIZE],
        }
    }
}
impl MemoryDriver for Memory {
    /// Returns an immutable byte slice of the memory driver's buffer.
    #[inline]
    fn buffer(&self) -> &[u8] {
        &self.buffer
    }

    /// Returns a mutable byte slice of the memory driver's buffer.
    #[inline]
    fn buffer_mut(&mut self) -> &mut [u8] {
        &mut self.buffer
    }

    /// Reads a value at a specific location in the virtual memory.
    fn read<T: Copy>(&self, pos: UInt) -> Result<T, NvmError> {
        let len = std::mem::size_of::<T>().try_into()?;
        if let Some(value) = self.buffer.get(<UInt as TryInto<usize>>::try_into(pos)?) {
            if let Some(end) = pos.checked_add(len) {
                if end <= self.buffer.len().try_into().unwrap_or(UInt::MAX) {
                    // SAFETY: We've bounds checked the value within `self.buffer`.
                    return unsafe { Ok(std::ptr::read_unaligned(addr_of!(*value).cast())) };
                }
            }
        }
        Err(NvmError::MemoryReadError { pos, len })
    }

    /// Writes a value to a specific location in the virtual memory.
    ///
    /// # Errors
    ///
    /// This operation is allowed to fail under any condition.
    #[inline]
    fn write<T: NoUninit>(&mut self, pos: UInt, value: &T) -> Result<(), NvmError> {
        self.write_bytes(pos, bytemuck::bytes_of(value))
    }

    /// Writes a slice of bytes to this memory at offset `pos`.
    fn write_bytes(&mut self, pos: UInt, buffer: &[u8]) -> Result<(), NvmError> {
        let len = buffer.len().try_into()?;
        if let Some(end) = pos.checked_add(len) {
            if let Some(buf) = self.buffer.get_mut(pos.try_into()?..end.try_into()?) {
                buf.copy_from_slice(buffer);
                return Ok(());
            }
        }
        Err(NvmError::MemoryWriteError { pos, len })
    }
}
