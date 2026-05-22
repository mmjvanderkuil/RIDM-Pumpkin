# Build
cargo build --release

# Run nqueens.rs example
cargo run --example nqueens -- 8

# Run minizinc
minizinc --solver pumpkin ./test.mzn