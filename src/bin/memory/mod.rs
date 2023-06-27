//! The virtual memory driver.
use nvm::{MemoryDriver, NvmError};
use std::ptr::addr_of;

/// The virtual memory driver.
pub struct Memory<'buf> {
    /// The buffer of memory to use as virtual machine RAM.
    buffer: &'buf mut [u8],
}
impl<'buf> Memory<'buf> {
    /// Creates a new memory driver using `buffer` as a virtual memory buffer.
    #[inline]
    pub fn new(buffer: &'buf mut [u8]) -> Self {
        Self { buffer }
    }
}
impl MemoryDriver for Memory<'_> {
    /// Reads a value at a specific location in the virtual memory.
    fn read<T: Copy>(&self, pos: usize) -> Result<T, NvmError> {
        if let Some(value) = self.buffer.get(pos) {
            if let Some(end) = pos.checked_add(core::mem::size_of::<T>()) {
                if end <= self.buffer.len() {
                    // SAFETY: We've bounds checked the value within `self.buffer`.
                    return unsafe { Ok(core::ptr::read_unaligned(addr_of!(*value).cast())) };
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
