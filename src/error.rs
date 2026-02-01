use crate::typecheck::TCError;

#[derive(Debug, Clone)]
pub(crate) enum SeferError {
    TCError(TCError),
}
