//! The virtual memory driver.
use bytemuck::NoUninit;
use nvm::{opcode::OpCode, MemoryDriver, NvmError};
use std::ptr::addr_of;

/// The virtual memory driver.
pub struct Memory {
    /// The buffer of memory to use as virtual machine RAM.
    buffer: [u8; Self::BYTE_COUNT],
}
impl Memory {
    /// A constant defining the amount of memory (in bytes) the memory driver has.
    const BYTE_COUNT: usize = (u8::MAX as usize).saturating_add(1);

    /// Creates a new memory driver using `buffer` as a virtual memory buffer.
    #[inline]
    pub const fn new() -> Self {
        Self {
            buffer: [OpCode::Exit as _; Self::BYTE_COUNT],
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

    /// Writes a value to a specific location in the virtual memory.
    ///
    /// # Errors
    ///
    /// This operation is allowed to fail under any condition.
    #[inline]
    fn write<T: NoUninit>(&mut self, pos: usize, value: &T) -> Result<(), NvmError> {
        self.write_bytes(pos, bytemuck::bytes_of(value))
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
