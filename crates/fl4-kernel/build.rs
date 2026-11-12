fn main() {
    // The image is linked outside cargo (xtask or the CMake drop-in) with
    // linker.ld, from this staticlib.
    println!("cargo:rerun-if-changed=linker.ld");
    println!("cargo:rerun-if-changed=src/boot.S");
}
