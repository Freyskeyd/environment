extern crate regex;
use regex::Regex;
use std::ffi::OsString;

/// Structure to deal with environment variables
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Environment {
    /// Customized environment variables
    vars: Vec<(OsString, OsString)>,
    /// Define if the structure must inherit
    inherit: bool,
    save_pattern: Option<String>,
}

impl Default for Environment {
    fn default() -> Self {
        Self {
            vars: vec![],
            inherit: false,
            save_pattern: None,
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
    /// use std::ffi::OsString;
    ///
    /// let e = environment::Environment::inherit().compile();
    /// let e_: Vec<(OsString, OsString)> = ::std::env::vars_os().collect();
    ///
    /// assert_eq!(e, e_);
    /// ```
    pub fn inherit() -> Self {
        Self {
            vars: vec![],
            inherit: true,
            save_pattern: None,
        }
    }

    /// Create a new Environment independent of the current process's Environment
    ///
    /// # Examples
    ///
    /// ```rust
    /// extern crate environment;
    ///
    /// let e = environment::Environment::empty().compile();
    /// assert_eq!(e, Vec::new());
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
    /// use std::ffi::OsString;
    ///
    /// let e = environment::Environment::empty().insert("foo", "bar").compile();
    /// assert_eq!(e, vec![(OsString::from("foo"), OsString::from("bar"))]);
    /// ```
    pub fn insert<S1: Into<OsString>, S2: Into<OsString>>(mut self, key: S1, val: S2) -> Self {
        self.vars.push((key.into(), val.into()));
        self
    }

    /// Define a regex that will be used to save some existing variables.
    /// It's only used when having an inherit equal to false.
    ///
    /// # Examples
    ///
    /// ```rust
    /// extern crate environment;
    ///
    /// use std::ffi::OsString;
    ///
    /// ::std::env::set_var("BAR", "BAZ");
    ///
    /// let e = environment::Environment::empty().insert("foo", "bar").compile();
    ///
    /// assert_eq!(e, vec![(OsString::from("foo"), OsString::from("bar"))]);
    ///
    /// let e = environment::Environment::empty().save("BAR").insert("foo", "bar").compile();
    ///
    /// assert_eq!(
    ///     e,
    ///     vec![
    ///         (OsString::from("BAR"), OsString::from("BAZ")),
    ///         (OsString::from("foo"), OsString::from("bar"))
    ///     ]
    /// );
    /// ```
    pub fn save<S: Into<String>>(mut self, pattern: S) -> Self {
        self.save_pattern = Some(pattern.into());

        self
    }

    /// Compile Environment object
    pub fn compile(self) -> Vec<(OsString, OsString)> {
        if self.inherit {
            ::std::env::vars_os().chain(self.vars).collect()
        } else {
            match self.save_pattern {
                Some(v) => {
                    let re = Regex::new(&v).unwrap();
                    ::std::env::vars_os()
                        .filter(|&(ref k, _)| re.is_match(k.to_str().unwrap()))
                        .chain(self.vars)
                        .collect()
                }
                None => self.vars,
            }
        }
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
            save_pattern: None,
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
            vec![(OsString::from("key"), OsString::from("value"))]
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
            vec![(OsString::from("key"), OsString::from("value"))]
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
    fn save_pattern() {
        let e: Environment = vec![("foo", "bar")].into();

        let mut c = Command::new("printenv");

        let output = c.env_clear()
            .envs(e.clone().save("PAT.*").compile())
            .output()
            .expect("failed to execute command");

        let output = String::from_utf8_lossy(&output.stdout);

        assert!(output.contains("foo=bar"));
        assert!(output.contains("PATH"));
    }
}
