//! Check for external package sources. Allow only vendorable packages.

use std::fs;
use std::path::Path;

/// List of allowed sources for packages.
const ALLOWED_SOURCES: &[&str] = &[
    "\"registry+https://github.com/rust-lang/crates.io-index\"",
    // HACK(eddyb) temporarily using my fork until `rust-lang/measureme#174` is merged
    "\"git+https://github.com/eddyb/measureme?branch=rdpmc-tweaks#42e97a6060700c4cf33c4ddca0725339e5d526fe\"",
];

/// Checks for external package sources. `root` is the path to the directory that contains the
/// workspace `Cargo.toml`.
pub fn check(root: &Path, bad: &mut bool) {
    // `Cargo.lock` of rust.
    let path = root.join("Cargo.lock");

    // Open and read the whole file.
    let cargo_lock = t!(fs::read_to_string(&path));

    // Process each line.
    for line in cargo_lock.lines() {
        // Consider only source entries.
        if !line.starts_with("source = ") {
            continue;
        }

        // Extract source value.
        let source = line.splitn(2, '=').nth(1).unwrap().trim();

        // Ensure source is allowed.
        if !ALLOWED_SOURCES.contains(&&*source) {
            println!("invalid source: {}", source);
            *bad = true;
        }
    }
}
