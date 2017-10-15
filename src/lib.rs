use std::collections::HashMap;
use std::ffi::OsString;
use std::iter::FromIterator;

/// Structure to deal with environment variables
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Environment {
    /// Customized environment variables
    vars: HashMap<OsString, OsString>,
    /// Define if the structure must inherit
    inherit: bool,
}

impl Default for Environment {
    fn default() -> Self {
        Self {
            vars: HashMap::new(),
            inherit: false,
        }
    }
}

impl Environment {
    /// Create a new Environment that inherits this process' environment.
    ///
    /// # Examples
    ///
    /// ```rust
    /// extern crate environment;
    ///
    /// use std::ffi::OsString;
    /// use std::collections::HashMap;
    ///
    /// let e = environment::Environment::inherit().compile();
    /// let e_: HashMap<OsString, OsString> = ::std::env::vars_os().collect();
    ///
    /// assert_eq!(e, e_);
    /// ```
    pub fn inherit() -> Self {
        Self {
            vars: HashMap::new(),
            inherit: true,
        }
    }

    /// Create a new Environment independent of the current process's Environment
    ///
    /// # Examples
    ///
    /// ```rust
    /// extern crate environment;
    ///
    /// use std::collections::HashMap;
    ///
    /// let e = environment::Environment::empty().compile();
    /// assert_eq!(e, HashMap::new());
    /// ```
    pub fn empty() -> Self {
        Self::default()
    }

    /// Insert a new entry into the custom variables for this environment object
    ///
    /// # Examples
    ///
    /// ```rust
    /// extern crate environment;
    ///
    /// use std::collections::HashMap;
    /// use std::ffi::OsString;
    /// use std::iter::FromIterator;
    ///
    /// let e = environment::Environment::empty().insert("foo", "bar").compile();
    /// assert_eq!(e, HashMap::from_iter(vec![(OsString::from("foo"), OsString::from("bar"))]));
    /// ```
    pub fn insert<S1: Into<OsString>, S2: Into<OsString>>(mut self, key: S1, val: S2) -> Self {
        self.vars.insert(key.into(), val.into());

        self
    }

    /// Compile Environment object
    pub fn compile(self) -> HashMap<OsString, OsString> {
        if self.inherit {
            ::std::env::vars_os().chain(self.vars).collect()
        } else {
            self.vars
        }
    }
}

impl<T: ToString, Z: ToString> FromIterator<(T, Z)> for Environment {
    fn from_iter<I: IntoIterator<Item = (T, Z)>>(iter: I) -> Self {
        Self {
            vars: iter.into_iter().map(|x| x.to_environment_tuple()).collect(),
            inherit: false,
        }
    }
}

impl<T: ToString, Z: ToString> Extend<(T, Z)> for Environment {
    fn extend<I: IntoIterator<Item = (T, Z)>>(&mut self, iter: I) {
        self.vars
            .extend(iter.into_iter().map(|x| x.to_environment_tuple()));
    }
}

/// Implicit clone for ergonomics
impl<'a> From<&'a Environment> for Environment {
    fn from(v: &'a Environment) -> Self {
        v.clone()
    }
}

pub trait EnvironmentItem {
    fn to_environment_tuple(&self) -> (OsString, OsString);
}

impl<T: ToString, Z: ToString> EnvironmentItem for (T, Z) {
    fn to_environment_tuple(&self) -> (OsString, OsString) {
        (
            OsString::from(self.0.to_string()),
            OsString::from(self.1.to_string()),
        )
    }
}

impl<'s, T: ToString, Z: ToString> EnvironmentItem for &'s (T, Z) {
    fn to_environment_tuple(&self) -> (OsString, OsString) {
        (
            OsString::from(self.0.to_string()),
            OsString::from(self.1.to_string()),
        )
    }
}

impl<'s, T> From<T> for Environment
where
    T: IntoIterator,
    T::Item: EnvironmentItem,
{
    fn from(v: T) -> Self {
        Self {
            vars: v.into_iter().map(|k| k.to_environment_tuple()).collect(),
            inherit: false,
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use std::process::Command;

    #[test]
    fn take_ownership() {
        let x = Environment::inherit();

        let mut c = Command::new("printenv");
        c.env_clear().envs(x.clone().compile()).envs(x.compile());
    }

    #[test]
    fn in_place_mod() {
        let y = Environment::empty();

        let y = y.insert("key", "value");

        assert_eq!(
            y.compile(),
            HashMap::from_iter(vec![(OsString::from("key"), OsString::from("value"))])
        );
    }

    #[test]
    fn in_place_mod2() {
        let x = Environment::inherit();

        let mut c = Command::new("printenv");

        let output = c.env_clear()
            .envs(x.insert("key", "value").insert("key", "vv").compile())
            .output()
            .expect("failed to execute command");

        let output = String::from_utf8_lossy(&output.stdout);

        assert!(output.contains("key=vv"));
        // Granted, `insert` moved `x`, so we can no longer reference it, even
        // though only a reference was passed to `envs`
    }

    #[test]
    fn in_place_mod3() {
        // In-place modification while allowing later accesses to the `Environment`
        let y = Environment::empty();

        assert_eq!(
            y.clone().insert("key", "value").compile(),
            HashMap::from_iter(vec![(OsString::from("key"), OsString::from("value"))])
        );

        let mut c = Command::new("printenv");

        let output = c.env_clear()
            .envs(y.compile())
            .output()
            .expect("failed to execute command");

        let output = String::from_utf8_lossy(&output.stdout);

        assert_eq!(output, "");
    }

    #[test]
    fn empty_env() {
        // In-place modification while allowing later accesses to the `Environment`
        let y = Environment::empty();

        let mut c = Command::new("printenv");

        let output = c.env_clear()
            .envs(y.compile())
            .output()
            .expect("failed to execute command");

        let output = String::from_utf8_lossy(&output.stdout);

        assert!(output.is_empty());
    }

    #[test]
    fn take_vec() {
        let v = vec![("bar", "baz")];

        let e: Environment = v.into();

        let mut c = Command::new("printenv");

        let output = c.env_clear()
            .envs(e.clone().compile())
            .output()
            .expect("failed to execute command");

        let output = String::from_utf8_lossy(&output.stdout);

        assert!(output.contains("bar=baz"));

        let mut c = Command::new("printenv");

        let output = c.env_clear()
            .envs(e.clone().insert("bar", "vv").compile())
            .output()
            .expect("failed to execute command");

        let output = String::from_utf8_lossy(&output.stdout);

        assert!(output.contains("bar=vv"));
        assert!(!output.contains("bar=baz"));
    }

    #[test]
    fn interger_value() {
        let v = vec![("bar", 0)];

        let _: Environment = v.into();
    }

    #[test]
    fn from_iterator() {
        let iter = (0..5).into_iter().map(|x| (format!("KEY_{}", x), x));

        let env = Environment::from_iter(iter);

        let expected: HashMap<OsString, OsString> = HashMap::from_iter(
            vec![
                ("KEY_0", "0"),
                ("KEY_1", "1"),
                ("KEY_2", "2"),
                ("KEY_3", "3"),
                ("KEY_4", "4"),
            ].into_iter()
                .map(|x| (x.0.into(), x.1.into()))
                .collect::<Vec<_>>(),
        );

        assert_eq!(env.compile(), expected);
    }

    #[test]
    fn extend_environment() {
        let v = vec![("bar", "baz")];
        let v2 = vec![("foo", "bar")];

        let mut env: Environment = v.clone().into();

        env.extend(v2.clone());

        let expected: HashMap<OsString, OsString> = v.into_iter()
            .chain(v2)
            .map(|x| (x.0.into(), x.1.into()))
            .collect();

        assert_eq!(env.compile(), expected);
    }
}
