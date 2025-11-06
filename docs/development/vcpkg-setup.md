# vcpkg Setup Guide

## Quick Start

ΛSNARK-R uses [vcpkg](https://github.com/microsoft/vcpkg) for C++ dependency management.

### Installation

```bash
# Clone vcpkg (if not already in project)
git clone https://github.com/microsoft/vcpkg.git

# Bootstrap vcpkg
./vcpkg/bootstrap-vcpkg.sh

# Install dependencies
./vcpkg/vcpkg install seal:x64-linux ntl:x64-linux gtest:x64-linux
```

### CMake Integration

```bash
cd cpp-core
cmake -B build \
    -DCMAKE_TOOLCHAIN_FILE=../vcpkg/scripts/buildsystems/vcpkg.cmake \
    -DCMAKE_BUILD_TYPE=Release \
    -DLAMBDA_SNARK_BUILD_TESTS=ON

cmake --build build -j$(nproc)
```

### Installed Packages

| Package | Version | Purpose                          |
|---------|---------|----------------------------------|
| SEAL    | 4.1+    | BFV encryption (LWE commitment)  |
| NTL     | 11.5+   | Number-theoretic transform (NTT) |
| GTest   | 1.14+   | Unit testing framework           |
| Eigen3  | 3.4+    | Matrix operations (optional)     |

### Troubleshooting

**Issue**: `seal` not found during CMake configuration
```bash
# Verify installation
./vcpkg/vcpkg list | grep seal

# Re-install if needed
./vcpkg/vcpkg remove seal
./vcpkg/vcpkg install seal:x64-linux
```

**Issue**: Build takes too long
```bash
# Use binary cache (vcpkg 2023.08.09+)
export VCPKG_BINARY_SOURCES="clear;default,readwrite"
```

**Issue**: Disk space warnings
```bash
# vcpkg uses ~2GB for SEAL + dependencies
du -sh vcpkg/
```

### Alternative: System Packages

For Debian/Ubuntu:
```bash
# NTL and GMP available via apt
sudo apt-get install libntl-dev libgmp-dev

# SEAL requires manual build or vcpkg
```

## Advanced Configuration

### Manifest Mode (Recommended for CI)

Create `vcpkg.json` in project root:
```json
{
  "name": "lambda-snark-r",
  "version-string": "0.1.0-alpha",
  "dependencies": [
    "seal",
    "ntl",
    "gtest",
    {
      "name": "eigen3",
      "version>=": "3.4.0"
    }
  ]
}
```

Then:
```bash
cmake -B build -DCMAKE_TOOLCHAIN_FILE=vcpkg/scripts/buildsystems/vcpkg.cmake
# vcpkg automatically installs dependencies from vcpkg.json
```

### Triplet Customization

For custom build flags (e.g., AVX-512):
```bash
# Create custom triplet: vcpkg/triplets/x64-linux-avx512.cmake
set(VCPKG_TARGET_ARCHITECTURE x64)
set(VCPKG_CRT_LINKAGE dynamic)
set(VCPKG_LIBRARY_LINKAGE static)
set(VCPKG_CMAKE_SYSTEM_NAME Linux)
set(VCPKG_CXX_FLAGS "-march=skylake-avx512")

# Use it
./vcpkg/vcpkg install seal:x64-linux-avx512
```

## References

- [vcpkg Documentation](https://vcpkg.io/)
- [Microsoft SEAL](https://github.com/microsoft/SEAL)
- [NTL Library](https://libntl.org/)
