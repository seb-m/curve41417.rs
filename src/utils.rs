// Crypto utils.
use std::num;
use std::num::Bitwise;
use std::ptr;
use std::rand::os::OsRng;
use std::slice::MutableVector;
use std::str;


pub trait ZeroMemory {
    fn zero_memory(self);
}

// Zero-out memory buffer.
#[allow(experimental)]
impl<'a, T> ZeroMemory for &'a mut [T] {
    fn zero_memory(self) {
        unsafe {
            // FIXME: use memset_s instead of a wrapper to memset, or maybe as
            // llvm intrinsics are internally synthesized it is maybe a sufficient
            // guarantee for corresponding code to be effectively emitted (to
            // confirm).
            ptr::zero_memory(self.as_mut_ptr(), self.len());
        }
    }
}

// Copy count elements from slice src to mutable slice dst.
// Requirement: count >= min(srclen, dstlen)
pub fn copy_slice_memory<T>(dst: &mut[T], src: &[T], count: uint) {
    assert!(dst.len() >= count && src.len() >= count);
    unsafe {
        ptr::copy_nonoverlapping_memory(dst.as_mut_ptr(), src.as_ptr(),
                                        count);
    }
}

// Return 1 iff x == y; 0 otherwise.
fn byte_eq(x: u8, y: u8) -> u8 {
    let mut z: u8 = !(x ^ y);
    z &= z >> 4;
    z &= z >> 2;
    z &= z >> 1;
    z
}

// Return true iff x == y; false otherwise.
pub fn bytes_eq(x: &[u8], y: &[u8]) -> bool {
    if x.len() != y.len() {
        return false;
    }

    let mut d: u8 = 0;
    for (&x1, &y1) in x.iter().zip(y.iter()) {
        d |= x1 ^ y1;
    }

    byte_eq(d, 0) == 1
}

// x and y are swapped iff cond is 1, there are left unchanged iff cond is 0.
// Currently only works for arrays of signed integers. cond is expected to
// be 0 or 1.
pub fn bytes_cswap<T: Signed + Primitive + Bitwise>(cond: T,
                                                    x: &mut [T],
                                                    y: &mut [T]) {
    assert_eq!(x.len(), y.len());

    let c: T = !(cond - num::one());
    for i in range(0, x.len()) {
        let t = c & (x[i] ^ y[i]);
        x[i] = x[i] ^ t;
        y[i] = y[i] ^ t;
    }
}

// Instanciate a secure RNG (based on urandom).
pub fn urandom_rng() -> OsRng {
    OsRng::new().unwrap()
}

// Return formatted hex string.
pub fn bytes_to_str_hex(v: &[u8]) -> String {
    let mut s: Vec<u8> = Vec::from_elem(v.len() * 2, 0u8);
    for i in range(0u, v.len()) {
        let digit = format!("{:02x}", v[i] as uint);
        *s.get_mut(i * 2 + 0) = digit.as_slice()[0];
        *s.get_mut(i * 2 + 1) = digit.as_slice()[1];
    }
    str::from_utf8(s.as_slice()).unwrap().to_string()
}


#[cfg(test)]
mod tests {
    use std::path::BytesContainer;
    use std::rand::random;
    use super::*;

    #[test]
    fn test_zero_memory() {
        struct Test {
            x: [u32, ..16],
        };

        let one = [1u32, ..16];
        let zero = [0u32, ..16];
        let mut s = Test {x: one};
        assert!(s.x == one);
        s.x.zero_memory();
        assert!(s.x == zero);
    }

    #[test]
    fn test_byte_eq() {
        for _ in range(0, 256) {
            let a: u8 = random();
            let b: u8 = random();
            assert_eq!(super::byte_eq(a, b) == 1, a == b);
        }
    }

    #[test]
    fn test_bytes_eq() {
        let a: [u8, ..64] = [0u8, ..64];
        let b: [u8, ..64] = [0u8, ..64];
        assert!(super::bytes_eq(a, b));

        for _ in range(0, 256) {
            let va = Vec::from_fn(64, |_| random::<u8>());
            let a = va.container_as_bytes();
            let vb = Vec::from_fn(64, |_| random::<u8>());
            let b = vb.container_as_bytes();
            assert_eq!(super::bytes_eq(a, b), a == b);
        }
    }

    #[test]
    fn test_bytes_cswap() {
        let mut a1: [i8, ..64] = [0i8, ..64];
        let a2 = a1;
        let mut b1: [i8, ..64] = [1i8, ..64];
        let b2 = b1;

        bytes_cswap(0, a1, b1);
        assert!(a1 == a2);
        assert!(b1 == b2);

        bytes_cswap(1, a1, b1);
        assert!(a1 == b2);
        assert!(b1 == a2);
    }
}
