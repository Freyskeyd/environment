# Environment

> **Handle environment variable context** - This crate helps you to deal with environment variables.

[![Build Status](https://travis-ci.org/Freyskeyd/environment.svg)](https://travis-ci.org/Freyskeyd/environment) [![Documentation](https://img.shields.io/badge/docs-master-blue.svg)][Documentation]

## Install

Just add it to your `Cargo.toml`:

```toml
[dependencies]
environment = "0.1"
```

## Example

Here's a trivial example:

```rust
extern crate environment;

use std::process::Command;

fn main() {
    let env = Environment::inherit().insert("foo", "bar");


    let mut c = Command::new("printenv");

    let output = c.env_clear()
        .envs(env.compile())
        .output()
        .expect("failed to execute command");

    let output = String::from_utf8_lossy(&output.stdout);

    assert!(output.contains("foo=bar"));

}
```

## License

Licensed under either of

 * Apache License, Version 2.0, ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
 * MIT license ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.

### Contribution

Unless you explicitly state otherwise, any contribution intentionally
submitted for inclusion in the work by you, as defined in the Apache-2.0
license, shall be dual licensed as above, without any additional terms or
conditions.

[Documentation]: https://docs.rs/environment
