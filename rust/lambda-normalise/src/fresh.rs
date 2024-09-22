use std::collections::HashMap;

/// Trait for introducing fresh names in case the current one
/// is already used.
pub trait Fresh
where
    Self: Sized,
{
    fn fresh_in_env<T>(&self, env: &HashMap<Self, T>) -> Self;
}

impl Fresh for String {
    fn fresh_in_env<T>(&self, env: &HashMap<Self, T>) -> Self {
        if !env.contains_key(self) {
            return self.clone();
        }

        for i in 0.. {
            let candidate = format!("{}{}", self, i);
            if !env.contains_key(&candidate) {
                return candidate;
            }
        }
        unreachable!()
    }
}
