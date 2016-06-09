@ECHO OFF

REM Please refer to https://github.com/briansmith/ring/blob/master/mk/appveyor.bat.

SETLOCAL EnableDelayedExpansion
SET VCVARSALL="C:\Program Files (x86)\Microsoft Visual Studio 14.0\VC\vcvarsall.bat"

ECHO Platform: %PLATFORM%

IF [%PLATFORM%] NEQ [x64] GOTO Win32
    SET ARCH=x86_64
    CALL %VCVARSALL% amd64
    IF %ERRORLEVEL% NEQ 0 EXIT 1
    GOTO Download
:Win32
IF [%PLATFORM%] NEQ [Win32] EXIT 1
    SET ARCH=i686
    CALL %VCVARSALL% amd64_x86
    IF %ERRORLEVEL% NEQ 0 EXIT 1
    GOTO Download

:Download
SET RUST_DIR=%APPVEYOR_BUILD_FOLDER%\rust
SET RUST_URL=https://static.rust-lang.org/dist/rust-%RUST%-%ARCH%-pc-windows-%ABI%.msi
IF EXIST %RUST_DIR% (
    ECHO Rust already installed in %RUST_DIR%
    DIR /A %RUST_DIR%
) ELSE (
    ECHO Going to download Rust from %RUST_URL% and install to %RUST_DIR%
    MKDIR build
    powershell -Command "(New-Object Net.WebClient).DownloadFile('%RUST_URL%', 'build\rust.msi')"
    IF %ERRORLEVEL% NEQ 0 EXIT 1

    START /W MSIEXEC /i build\rust.msi INSTALLDIR="%RUST_DIR%" /quiet /qn /norestart
    IF %ERRORLEVEL% NEQ 0 EXIT 1
)

SET PATH=%RUST_DIR%\bin;%PATH%

@ECHO ON

LINK /HELP
CL
rustc --version
cargo --version

cargo build
IF %ERRORLEVEL% NEQ 0 EXIT 1

cargo test
IF %ERRORLEVEL% NEQ 0 EXIT 1

cargo bench
IF %ERRORLEVEL% NEQ 0 EXIT 1

cargo test --manifest-path extprim_tests\Cargo.toml
IF %ERRORLEVEL% NEQ 0 EXIT 1

