//! The virtual memory driver.
use nvm::{opcode::OpCode, MemoryDriver, NvmError, StackDriver};
use std::ptr::{addr_of, addr_of_mut};

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
            buffer: [OpCode::EXIT; Self::BYTE_COUNT],
        }
    }
}
impl MemoryDriver for Memory {
    /// The memory driver's stack driver type.
    type StackDriver<'stack> = Stack<'stack>;

    /// Returns an immutable byte slice of the memory driver's buffer.
    #[inline]
    fn buffer(&self) -> &[u8] {
        &self.buffer
    }

    /// Returns the stack memory driver.
    fn stack_driver(&mut self) -> Result<Self::StackDriver<'_>, NvmError> {
        let start = Self::BYTE_COUNT
            .checked_sub(64)
            .ok_or(NvmError::OverflowError)?;
        Ok(Stack {
            stack: self
                .buffer
                .get_mut(start..)
                .ok_or(NvmError::GetStackError)?,
        })
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

/// The virtual stack driver.
pub struct Stack<'stack> {
    /// A mutable slice of the stack's memory.
    stack: &'stack mut [u8],
}
impl StackDriver for Stack<'_> {
    /// Reads a [usize] value from a specific location in the virtual stack.
    fn read(&self, pos: usize) -> Result<usize, NvmError> {
        let len = self.stack.len();
        if let Some(pos) = len.checked_sub(pos) {
            if let Some(byte_ref) = self.stack.get(pos) {
                if let Some(end) = pos.checked_add(std::mem::size_of::<usize>()) {
                    if end <= len {
                        #[allow(clippy::ptr_as_ptr)]
                        // SAFETY: We've bounds checked the value within `self.stack`.
                        return unsafe { Ok(std::ptr::read_unaligned(addr_of!(*byte_ref) as _)) };
                    }
                }
            }
        }
        Err(NvmError::StackReadError { pos })
    }

    /// Writes a [usize] value to a specific location in the virtual stack.
    fn write(&mut self, pos: usize, value: usize) -> Result<(), NvmError> {
        let len = self.stack.len();
        if let Some(pos) = len
            .checked_sub(pos)
            .and_then(|pos| pos.checked_sub(std::mem::size_of::<usize>()))
        {
            if let Some(byte_ref) = self.stack.get_mut(pos) {
                if let Some(end) = pos.checked_add(std::mem::size_of::<usize>()) {
                    if end <= len {
                        // SAFETY: We've bounds checked the write within `self.stack`.
                        unsafe {
                            #[allow(clippy::ptr_as_ptr)]
                            std::ptr::write_unaligned(addr_of_mut!(*byte_ref) as _, value);
                        }
                        return Ok(());
                    }
                }
            }
        }
        Err(NvmError::StackWriteError { pos })
    }
}
