use core::fmt::Debug;

use crate::Token;

#[derive(thiserror::Error, Debug)]
pub enum Error {
    #[error("Not a root node")]
    NotARootNode,
    #[error("Token does not correspond to a node in the arena: {0:?}")]
    TokenNotInArena(Token),
    #[error("Corrupt arena")]
    CorruptArena,
    #[error("Stale token: {0:?} is not found in the arena. Check code")]
    StaleToken(Token),
    #[error("Cannot insert as the previous sibling of the root node")]
    CannotInsert,
}

pub type Result<T = ()> = core::result::Result<T, self::Error>;
