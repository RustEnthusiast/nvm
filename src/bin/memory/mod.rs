//! The virtual memory driver.
use nvm::{opcode::OpCode, MemoryDriver, NvmError};
use std::ptr::addr_of;

/// The virtual memory driver.
pub struct Memory {
    /// The buffer of memory to use as virtual machine RAM.
    buffer: [u8; u8::MAX as _ + 1],
}
impl Memory {
    /// Creates a new memory driver using `buffer` as a virtual memory buffer.
    #[inline]
    pub const fn new() -> Self {
        Self {
            buffer: [OpCode::EXIT; u8::MAX as _],
        }
    }
}
impl MemoryDriver for Memory {
    /// Reads a value at a specific location in the virtual memory.
    fn read<T: Copy>(&self, pos: usize) -> Result<T, NvmError> {
        if let Some(value) = self.buffer.get(pos) {
            if let Some(end) = pos.checked_add(std::mem::size_of::<T>()) {
                if end <= self.buffer.len() {
                    // SAFETY: We've bounds checked the value within `self.buffer`.
                    return unsafe { Ok(std::ptr::read_unaligned(addr_of!(*value).cast())) };
                }
            }
        }
        Err(NvmError::MemoryReadError {
            pos,
            len: std::mem::size_of::<T>(),
        })
    }

    /// Writes a slice of bytes to this memory at offset `pos`.
    fn write_bytes(&mut self, pos: usize, buffer: &[u8]) -> Result<(), NvmError> {
        if let Some(end) = pos.checked_add(buffer.len()) {
            if let Some(buf) = self.buffer.get_mut(pos..end) {
                buf.copy_from_slice(buffer);
                return Ok(());
            }
        }
        Err(NvmError::MemoryWriteError {
            pos,
            len: buffer.len(),
        })
    }
}
