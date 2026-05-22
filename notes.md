# Build
cargo build --release

# Run nqueens.rs example
cargo run --example nqueens -- 8

# Run minizinc
minizinc --solver pumpkin ./test.mzn
minizinc --solver pumpkin ./learned_nogood.mzn