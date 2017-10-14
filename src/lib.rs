use std::ffi::OsString;
use std::iter::FromIterator;

/// Structure that represent a unique Variable.
#[derive(Clone, Debug)]
pub struct Var {
    /// The variable's key.
    key: OsString,
    /// The variable's value.
    value: OsString,
    /// Conditional statement for this variable.
    condition: bool,
    /// The environment that own the variable.
    environment: Environment,
}

impl Var {
    /// Check if the Var's value is strictly different of the input.
    ///
    /// # Examples
    ///
    /// ```rust
    /// extern crate environment;
    ///
    /// let var: environment::Var = ("FOO", "BAR").into();
    ///
    /// assert_eq!(var.clone().isnt("BAR").assign("BAZ").var("FOO"), var);
    /// ```
    pub fn isnt<T: ToString>(mut self, value: T) -> Self {
        self.condition = self.value != OsString::from(value.to_string());

        self
    }

    /// Check if the Var's value is strictly equal to the input.
    ///
    /// # Examples
    ///
    /// ```rust
    /// extern crate environment;
    ///
    /// let var: environment::Var = ("FOO", "BAR").into();
    ///
    /// assert_eq!(var.clone().is("BAZ").assign("BAZ").var("FOO"), var);
    /// ```
    pub fn is<T: ToString>(mut self, value: T) -> Self {
        self.condition = self.value == OsString::from(value.to_string());

        self
    }

    /// Assign a new value to the variable.
    ///
    /// Note: assigning can be conditioned by
    /// [is](struct.Var.html#method.is) or [isnt](struct.Var.html#method.isnt)
    ///
    /// # Examples
    ///
    /// ```rust
    /// extern crate environment;
    ///
    /// let var: environment::Var = ("FOO", "BAR").into();
    ///
    /// assert_eq!(var.clone().is("BAZ").assign("BAZ").var("FOO"), var);
    ///
    /// assert!(var.clone().isnt("BAZ").assign("BAZ").var("FOO") != var);
    ///
    /// ```
    pub fn assign<T: ToString>(mut self, value: T) -> Environment {
        if self.condition {
            self.value = OsString::from(value.to_string());
        }

        self.environment.vars.push((self.key, self.value));

        self.environment
    }

    /// Clear the value of a variable.
    ///
    /// Note: clearing can be conditioned by
    /// [is](struct.Var.html#method.is) or [isnt](struct.Var.html#method.isnt)
    ///
    /// # Examples
    ///
    /// ```rust
    /// extern crate environment;
    ///
    /// let var: environment::Var = ("FOO", "BAR").into();
    ///
    /// assert_eq!(var.clone().is("BAR").clear().var("FOO"), ("FOO", "").into());
    ///
    /// assert_eq!(var.clone().isnt("BAR").clear().var("FOO"), var);
    ///
    /// ```
    pub fn clear(mut self) -> Environment {
        if self.condition {
            self.value.clear();
        }

        self.environment.vars.push((self.key, self.value));

        self.environment
    }

    /// Append a value to the current variable's value.
    ///
    /// Note: appending can be conditioned by
    /// [is](struct.Var.html#method.is) or [isnt](struct.Var.html#method.isnt)
    ///
    /// # Examples
    ///
    /// ```rust
    /// extern crate environment;
    ///
    /// let var: environment::Var = ("FOO", "BAR").into();
    ///
    /// assert_eq!(var.clone().is("BAR").append("BAZ").var("FOO"), ("FOO", "BARBAZ").into());
    ///
    /// assert_eq!(var.clone().isnt("BAR").append("BAZ").var("FOO"), var);
    ///
    /// ```
    pub fn append<T: ToString>(mut self, value: T) -> Environment {
        if self.condition {
            self.value.push(value.to_string());
        }

        self.environment.vars.push((self.key, self.value));

        self.environment
    }

    /// Define the variable's value equal to the system variable.
    ///
    /// Note: inheriting can be conditioned by
    /// [is](struct.Var.html#method.is) or [isnt](struct.Var.html#method.isnt)
    ///
    /// # Examples
    ///
    /// ```rust
    /// extern crate environment;
    ///
    /// ::std::env::set_var("FOO", "BAR");
    ///
    /// let var: environment::Var = ("FOO", "BAZ").into();
    ///
    /// assert_eq!(var.clone().is("BAZ").inherit().var("FOO"), ("FOO", "BAR").into());
    /// assert_eq!(var.clone().isnt("BAZ").inherit().var("FOO"), ("FOO", "BAZ").into());
    ///
    /// ```
    pub fn inherit(mut self) -> Environment {
        if self.condition {
            self.value = if let Some(v) = ::std::env::vars_os()
                .filter(|&(ref k, _)| k == &self.key)
                .collect::<Vec<(OsString, OsString)>>()
                .first()
            {
                v.1.clone()
            } else {
                OsString::new()
            };
        }

        self.environment.vars.push((self.key, self.value));

        self.environment
    }
}

impl<T: ToString, Z: ToString> From<(T, Z)> for Var {
    fn from(v: (T, Z)) -> Self {
        Self {
            key: OsString::from(v.0.to_string()),
            value: OsString::from(v.1.to_string()),
            condition: true,
            environment: Environment::empty(),
        }
    }
}

impl PartialEq for Var {
    fn eq(&self, other: &Self) -> bool {
        (&self.key, &self.value) == (&other.key, &other.value)
    }
}

/// Structure to deal with environment variables
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Environment {
    /// Customized environment variables
    vars: Vec<(OsString, OsString)>,
    /// Define if the structure must inherit
    inherit: bool,
}

impl Default for Environment {
    fn default() -> Self {
        Self {
            vars: vec![],
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

    /// Compile Environment object
    pub fn compile(self) -> Vec<(OsString, OsString)> {
        if self.inherit {
            ::std::env::vars_os().chain(self.vars).collect()
        } else {
            self.vars
        }
    }

    pub fn with_var<T: Into<Var>>(mut self, v: T) -> Environment {
        let var = v.into();
        self.vars.push((var.key, var.value));

        self
    }

    pub fn var<T: ToString>(self, key: T) -> Var {
        let key = OsString::from(key.to_string());

        Var {
            key: key.clone(),
            value: if self.inherit {
                if let Some(v) = ::std::env::vars_os()
                    .chain(self.vars.clone())
                    .filter(|&(ref k, _)| k == &key)
                    .collect::<Vec<(OsString, OsString)>>()
                    .last()
                {
                    v.1.clone()
                } else {
                    OsString::new()
                }
            } else if let Some(v) = self.vars
                .clone()
                .into_iter()
                .filter(|&(ref k, _)| k == &key)
                .collect::<Vec<(OsString, OsString)>>()
                .last()
            {
                v.1.clone()
            } else {
                OsString::new()
            },
            condition: true,
            environment: self,
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
    fn interger_value() {
        let v = vec![("bar", 0)];

        let _: Environment = v.into();
    }

    #[test]
    fn from_iterator() {
        let iter = (0..5).into_iter().map(|x| (format!("KEY_{}", x), x));

        let env = Environment::from_iter(iter);

        let expected: Vec<(OsString, OsString)> = vec![
            ("KEY_0", "0"),
            ("KEY_1", "1"),
            ("KEY_2", "2"),
            ("KEY_3", "3"),
            ("KEY_4", "4"),
        ].into_iter()
            .map(|x| (x.0.into(), x.1.into()))
            .collect();

        assert_eq!(env.compile(), expected);
    }

    #[test]
    fn extend_environment() {
        let v = vec![("bar", "baz")];
        let v2 = vec![("foo", "bar")];

        let mut env: Environment = v.clone().into();

        env.extend(v2.clone());

        let expected: Vec<(OsString, OsString)> = v.into_iter()
            .chain(v2)
            .map(|x| (x.0.into(), x.1.into()))
            .collect();

        assert_eq!(env.compile(), expected);
    }

    #[test]
    fn var_init() {
        let v: Var = ("KEY", "VALUE").into();
        let v2 = Var {
            environment: Environment::empty(),
            condition: true,
            key: "KEY".into(),
            value: "VALUE".into(),
        };

        assert_eq!(v, v2);
    }

    #[test]
    fn environment_var() {
        let v: Var = ("FOO", "BAR").into();

        ::std::env::set_var("FOO", "BAR");

        let e = Environment::inherit();
        assert_eq!(v, e.var("FOO"));

        ::std::env::remove_var("FOO");
        assert!(::std::env::var_os("FOO") == None);
    }

    #[test]
    fn environment_var_2() {
        assert!(::std::env::var_os("FOO") == None);

        let e_based = Environment::inherit().insert("FOO", "BAR");

        let e = Environment::inherit();
        assert_eq!(e_based, e.var("FOO").assign("BAR"));

        ::std::env::remove_var("FOO");
        assert!(::std::env::var_os("FOO") == None);
    }

    #[test]
    fn environment_var_append() {
        assert!(::std::env::var_os("FOO") == None);

        let v: Var = ("FOO", "BARBAZ").into();

        ::std::env::set_var("FOO", "BAR");

        let e = Environment::inherit();
        assert_eq!(v, e.var("FOO").append("BAZ").var("FOO"));

        ::std::env::remove_var("FOO");
        assert!(::std::env::var_os("FOO") == None);
    }

    #[test]
    fn environment_var_clear() {
        assert!(::std::env::var_os("FOO") == None);

        let v: Var = ("FOO", "").into();

        ::std::env::set_var("FOO", "BAR");

        let e = Environment::inherit();
        assert_eq!(v, e.var("FOO").clear().var("FOO"));

        ::std::env::remove_var("FOO");
        assert!(::std::env::var_os("FOO") == None);
    }

    #[test]
    fn environment_var_replace_if() {
        assert!(::std::env::var_os("FOO") == None);

        ::std::env::set_var("FOO", "BAR");

        let e = Environment::inherit();

        assert_eq!(
            e.clone().var("FOO").is("BAR").assign("BAZ").var("FOO"),
            ("FOO", "BAZ").into()
        );

        assert_eq!(
            e.clone().var("FOO").isnt("BAZ").assign("BAZ").var("FOO"),
            ("FOO", "BAZ").into()
        );

        assert_eq!(
            e.var("FOO").isnt("BAR").assign("BAZ").var("FOO"),
            ("FOO", "BAR").into()
        );

        ::std::env::remove_var("FOO");
        assert!(::std::env::var_os("FOO") == None);
    }

    #[test]
    fn environment_var_clear_if() {
        assert!(::std::env::var_os("FOO") == None);

        ::std::env::set_var("FOO", "BAR");

        let e = Environment::inherit();

        assert_eq!(
            e.clone().var("FOO").is("BAR").clear().var("FOO"),
            ("FOO", "").into()
        );

        assert_eq!(
            e.var("FOO").isnt("BAR").clear().var("FOO"),
            ("FOO", "BAR").into()
        );

        ::std::env::remove_var("FOO");
        assert!(::std::env::var_os("FOO") == None);
    }

    #[test]
    fn environment_var_append_if() {
        assert!(::std::env::var_os("FOO") == None);

        ::std::env::set_var("FOO", "BAR");

        let e = Environment::inherit();

        assert_eq!(
            e.clone().var("FOO").is("BAR").append("BAZ").var("FOO"),
            ("FOO", "BARBAZ").into()
        );

        assert_eq!(
            e.var("FOO").isnt("BAR").append("BAZ").var("FOO"),
            ("FOO", "BAR").into()
        );

        ::std::env::remove_var("FOO");
        assert!(::std::env::var_os("FOO") == None);
    }

    #[test]
    fn complete_environment() {
        let env = Environment::inherit()
            .var("FOO").assign("BAR") // Assign a value to FOO (i.e. : FOO=BAR)
            .var("FOO").append("BAZ") // Append a value to FOO (i.e. : FOO=BARBAZ)
            .var("FOO").clear() // Clear the value of FOO (i.e. : FOO="")
            .var("FOO").assign("BAR")
            .var("FOO").is("BAR").clear() // Clear the value if FOO is BAR (i.e. : FOO="")
            .var("FOO").assign("BAZ")
            .var("FOO").isnt("BAR").clear() // Clear the value if FOO isnt BAR (i.e. : FOO="")
            .var("FOO").isnt("BAR").append("BAZ"); // Append a value to FOO (i.e : FOO=BAZ)

        assert_eq!(env.var("FOO"), ("FOO", "BAZ").into());
    }

    #[test]
    fn use_var() {
        let v: Var = ("FOO", "BAR").into();

        Environment::empty().with_var(v);
    }

    #[test]
    fn readme_example() {
        let foo: Var = ("FOO", "BAR").into();

        let env = Environment::inherit()
            .with_var(foo)
            .var("FOO")
            .is("BAR")
            .append("BAZ");

        let mut c = Command::new("printenv");

        let output = c.env_clear()
            .envs(env.compile())
            .output()
            .expect("failed to execute command");

        let output = String::from_utf8_lossy(&output.stdout);

        assert!(output.contains("FOO=BARBAZ"));
    }
}
