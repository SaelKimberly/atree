//! A module that contains different kinds of iterators.
use alloc::collections::VecDeque;
use core::marker::PhantomData;
use core::mem;

use crate::node::Node;
use crate::token::Token;
use crate::{Arena, Error, Result};

/// A flag for the branch the next iteration should take when traversing the
/// tree. See [`preorder_next`] and [`postorder_next`] for usage.
///
/// [`preorder_next`]: fn.preorder_next.html
/// [`postorder_next`]: fn.postorder_next.html
#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) enum Branch {
    /// The sibling branch
    Sibling,
    /// The child branch
    Child,
    /// End of iteration
    None,
}

/// The order in which tree traversal takes place.
#[derive(Clone, Copy)]
pub enum TraversalOrder {
    /// Pre-order (depth-first traversal)
    Pre,
    /// Post-order (depth-first traversal)
    Post,
    /// Level-order (breadth-first traversal)
    Level,
}

/// A helper function to find the next node in the tree during preorder
/// traversal. To be used with [`depth_first_tokens_next`].
///
/// [`depth_first_tokens_next`]: fn.depth_first_tokens_next.html
pub(crate) fn preorder_next<T>(
    mut node_token: Token,
    root: Token,
    mut branch: Branch,
    arena: &Arena<T>,
) -> Result<(Option<Token>, Branch)> {
    loop {
        let node = arena.get(node_token)?;
        match branch {
            Branch::None => unreachable!(), // unreachable
            Branch::Child => match node.first_child {
                Some(token) => break Ok((Some(token), Branch::Child)),
                None => match node_token == root {
                    true => break Ok((None, Branch::None)),
                    false => branch = Branch::Sibling,
                },
            },
            Branch::Sibling => match node.next_sibling {
                Some(token) => break Ok((Some(token), Branch::Child)),
                None => match node.parent {
                    None => break Ok((None, Branch::None)),
                    Some(parent) => match parent == root {
                        true => break Ok((None, Branch::None)),
                        false => {
                            node_token = parent;
                            branch = Branch::Sibling;
                        }
                    },
                },
            },
        }
    }
}

/// A helper function to find the next node in the tree during postorder
/// traversal. To be used with [`depth_first_tokens_next`].
///
/// [`depth_first_tokens_next`]: fn.depth_first_tokens_next.html
pub(crate) fn postorder_next<T>(
    mut node_token: Token,
    root: Token,
    mut branch: Branch,
    arena: &Arena<T>,
) -> Result<(Option<Token>, Branch)> {
    let mut switch_branch = true;
    loop {
        let node = arena.get(node_token)?;
        match branch {
            Branch::None => break Ok((None, Branch::None)),
            Branch::Child => match node.first_child {
                Some(token) => {
                    node_token = token;
                    switch_branch = false;
                }
                None => match switch_branch {
                    false => break Ok((Some(node_token), Branch::Sibling)),
                    true => match node_token == root {
                        true => break Ok((Some(root), Branch::None)), // no descendants
                        false => branch = Branch::Sibling,
                    },
                },
            },
            Branch::Sibling => match node.next_sibling {
                Some(token) => {
                    switch_branch = false;
                    node_token = token;
                    branch = Branch::Child;
                }
                None => match node.parent {
                    None => break Ok((None, Branch::Child)),
                    Some(parent) => match parent == root {
                        true => break Ok((Some(root), Branch::None)),
                        false => break Ok((Some(parent), Branch::Sibling)),
                    },
                },
            },
        }
    }
}

/// A function to be curried at the call-site. Used in [`subtree_tokens`] for
/// the construction of [`SubtreeTokens`].
///
/// [`subtree_tokens`]: ../struct.Token.html#method.subtree_tokens
/// [`SubtreeTokens`]: struct.SubtreeTokens.html
#[allow(clippy::type_complexity)]
pub(crate) fn depth_first_tokens_next<'a, T>(
    iter: &mut SubtreeTokens<'a, T>,
    func: fn(Token, Token, Branch, &Arena<T>) -> Result<(Option<Token>, Branch)>,
) -> Result<Option<Token>> {
    match iter.node_token {
        None => Ok(None),
        Some(token) => match iter.arena.get(token) {
            Err(_) => Err(Error::StaleToken(token)),
            Ok(_) => match func(token, iter.subtree_root, iter.branch, iter.arena) {
                Ok((next_node, branch)) => {
                    iter.node_token = next_node;
                    iter.branch = branch;
                    Ok(Some(token))
                }
                Err(e) => Err(e),
            },
        },
    }
}

/// A function to be curried at the call-site. Used in [`subtree_tokens`] for
/// the construction of [`SubtreeTokens`].
///
/// [`subtree_tokens`]: ../struct.Token.html#method.subtree_tokens
/// [`SubtreeTokens`]: struct.SubtreeTokens.html
pub(crate) fn breadth_first_tokens_next<'a, T>(
    iter: &mut SubtreeTokens<'a, T>,
) -> Result<Option<Token>> {
    match iter.curr_level.pop_front() {
        Some(token) => {
            iter.next_level.extend(token.children_tokens(iter.arena)?);
            Ok(Some(token))
        }
        None => match iter.next_level.is_empty() {
            true => Ok(None),
            false => {
                mem::swap(&mut iter.curr_level, &mut iter.next_level);
                Ok(iter.next())
            }
        },
    }
}

/// An iterator of tokens of the subtree nodes of a given node.
///
/// This `struct` is created by the `subtree_tokens` methods on [`Token`]
/// and [`Node`]. See their documentation for more.
///
/// [`Token`]: ../struct.Token.html#method.subtree_tokens
/// [`Node`]: ../struct.Node.html#method.subtree_tokens
pub struct SubtreeTokens<'a, T> {
    pub(crate) arena: &'a Arena<T>,
    pub(crate) subtree_root: Token,
    pub(crate) node_token: Option<Token>,
    pub(crate) branch: Branch,
    pub(crate) curr_level: VecDeque<Token>,
    pub(crate) next_level: VecDeque<Token>,
    pub(crate) next: fn(&mut SubtreeTokens<'a, T>) -> Result<Option<Token>>,
}

impl<'a, T> Iterator for SubtreeTokens<'a, T> {
    type Item = Token;
    fn next(&mut self) -> Option<Self::Item> {
        match (self.next)(self) {
            Ok(Some(token)) => Some(token),
            _ => None,
        }
    }
}

/// An iterator of references of the subtree nodes of a given node.
///
/// This `struct` is created by the `subtree` methods on [`Token`]
/// and [`Node`]. See their documentation for more.
///
/// [`Token`]: ../struct.Token.html#method.subtree
/// [`Node`]: ../struct.Node.html#method.subtree
pub struct Subtree<'a, T> {
    pub(crate) arena: &'a Arena<T>,
    pub(crate) iter: SubtreeTokens<'a, T>,
}

impl<'a, T> Iterator for Subtree<'a, T> {
    type Item = &'a Node<T>;
    fn next(&mut self) -> Option<&'a Node<T>> {
        match self.iter.next() {
            Some(node_token) => self.arena.get(node_token).ok(),
            _ => None,
        }
    }
}

/// An iterator of mutable references of the subtree nodes of a given node.
///
/// This `struct` is created by the [`subtree_mut`] method on `Token`. See
/// its documentation for more.
///
/// [`subtree_mut`]: ../struct.Token.html#method.subtree_mut
pub struct SubtreeMut<'a, T: 'a> {
    pub(crate) arena: *mut Arena<T>,
    pub(crate) iter: SubtreeTokens<'a, T>,
    pub(crate) marker: PhantomData<&'a mut T>,
}

impl<'a, T> Iterator for SubtreeMut<'a, T> {
    type Item = &'a mut Node<T>;
    fn next(&mut self) -> Option<&'a mut Node<T>> {
        match self.iter.next() {
            None => None,
            Some(node_token) => {
                let arena = unsafe {
                    self.arena
                        .as_mut()
                        .expect("Arena pointer should not be null")
                };
                arena.get_mut(node_token).ok()
            }
        }
    }
}

unsafe impl<T: Sync> Sync for SubtreeMut<'_, T> {}
unsafe impl<T: Send> Send for SubtreeMut<'_, T> {}

/// An iterator of tokens of siblings that follow a given node.
///
/// This `struct` is created by the `following_siblings_tokens` methods on
/// [`Token`] and [`Node`]. See their documentation for more.
///
/// [`Token`]: ../struct.Token.html#method.following_siblings_tokens
/// [`Node`]: ../struct.Node.html#method.following_siblings_tokens
pub struct FollowingSiblingTokens<'a, T> {
    pub(crate) arena: &'a Arena<T>,
    pub(crate) node_token: Option<Token>,
}

/// An iterator of tokens of siblings that precede a given node.
///
/// This `struct` is created by the `preceding_siblings_tokens` methods on
/// [`Token`] and [`Node`]. See their documentation for more.
///
/// [`Token`]: ../struct.Token.html#method.preceding_siblings_tokens
/// [`Node`]: ../struct.Node.html#method.preceding_siblings_tokens
pub struct PrecedingSiblingTokens<'a, T> {
    pub(crate) arena: &'a Arena<T>,
    pub(crate) node_token: Option<Token>,
}

/// An iterator of tokens of the children of a given node.
///
/// This `struct` is created by the `children_tokens` methods on
/// [`Token`] and [`Node`]. See their documentation for more.
///
/// [`Token`]: ../struct.Token.html#method.children_tokens
/// [`Node`]: ../struct.Node.html#method.children_tokens
pub struct ChildrenTokens<'a, T> {
    pub(crate) arena: &'a Arena<T>,
    pub(crate) node_token: Option<Token>,
}

/// An iterator of tokens of the ancestors of a given node.
///
/// This `struct` is created by the `ancestors_tokens` methods on
/// [`Token`] and [`Node`]. See their documentation for more.
///
/// [`Token`]: ../struct.Token.html#method.ancestors_tokens
/// [`Node`]: ../struct.Node.html#method.ancestors_tokens
pub struct AncestorTokens<'a, T> {
    pub(crate) arena: &'a Arena<T>,
    pub(crate) node_token: Option<Token>,
}

/// An iterator of references to siblings that precede a given node.
///
/// This `struct` is created by the `preceding_siblings` methods on
/// [`Token`] and [`Node`]. See their documentation for more.
///
/// [`Token`]: ../struct.Token.html#method.preceding_siblings
/// [`Node`]: ../struct.Node.html#method.preceding_siblings
pub struct PrecedingSiblings<'a, T> {
    pub(crate) token_iter: PrecedingSiblingTokens<'a, T>,
}

/// An iterator of references to siblings that follow a given node.
///
/// This `struct` is created by the `following_siblings` methods on
/// [`Token`] and [`Node`]. See their documentation for more.
///
/// [`Token`]: ../struct.Token.html#method.following_siblings
/// [`Node`]: ../struct.Node.html#method.following_siblings
pub struct FollowingSiblings<'a, T> {
    pub(crate) token_iter: FollowingSiblingTokens<'a, T>,
}

/// An iterator of references to the children of a given node.
///
/// This `struct` is created by the `children` methods on
/// [`Token`] and [`Node`]. See their documentation for more.
///
/// [`Token`]: ../struct.Token.html#method.children
/// [`Node`]: ../struct.Node.html#method.children
pub struct Children<'a, T> {
    pub(crate) token_iter: ChildrenTokens<'a, T>,
}

/// An iterator of references to the ancestors of a given node.
///
/// This `struct` is created by the `ancestors` methods on
/// [`Token`] and [`Node`]. See their documentation for more.
///
/// [`Token`]: ../struct.Token.html#method.ancestors
/// [`Node`]: ../struct.Node.html#method.ancestors
pub struct Ancestors<'a, T> {
    pub(crate) token_iter: AncestorTokens<'a, T>,
}

/// An iterator of mutable references to siblings that precede a given node.
///
/// This `struct` is created by the [`preceding_siblings_mut`] method on
/// `Token`. See its documentation for more.
///
/// [`preceding_siblings_mut`]: ../struct.Token.html#method.preceding_siblings_mut
pub struct PrecedingSiblingsMut<'a, T: 'a> {
    pub(crate) arena: *mut Arena<T>,
    pub(crate) node_token: Option<Token>,
    pub(crate) marker: PhantomData<&'a mut T>,
}

/// An iterator of mutable references to siblings that follow a given node.
///
/// This `struct` is created by the [`following_siblings_mut`] method on
/// `Token`. See its documentation for more.
///
/// [`following_siblings_mut`]: ../struct.Token.html#method.following_siblings_mut
pub struct FollowingSiblingsMut<'a, T: 'a> {
    pub(crate) arena: *mut Arena<T>,
    pub(crate) node_token: Option<Token>,
    pub(crate) marker: PhantomData<&'a mut T>,
}

/// An iterator of mutable references to the children of a given node.
///
/// This `struct` is created by the [`children_mut`] method on
/// `Token`. See its documentation for more.
///
/// [`children_mut`]: ../struct.Token.html#method.children_mut
pub struct ChildrenMut<'a, T: 'a> {
    pub(crate) arena: *mut Arena<T>,
    pub(crate) node_token: Option<Token>,
    pub(crate) marker: PhantomData<&'a mut T>,
}

/// An iterator of mutable references to the ancestors of a given node.
///
/// This `struct` is created by the [`ancestors_mut`] method on
/// `Token`. See its documentation for more.
///
/// [`ancestors_mut`]: ../struct.Token.html#method.ancestors_mut
pub struct AncestorsMut<'a, T: 'a> {
    pub(crate) arena: *mut Arena<T>,
    pub(crate) node_token: Option<Token>,
    pub(crate) marker: PhantomData<&'a mut T>,
}

/// A macro that implements the `Iterator` trait on iterators (aside from ones
/// related to subtree traversal.
macro_rules! iterator {
    (@token struct $name:ident > $field:ident) => {
        impl<'a, T> Iterator for $name<'a, T> {
            type Item = Token;
            fn next(&mut self) -> Option<Self::Item> {
                match self.node_token {
                    None => None,
                    Some(token) => match self.arena.get(token) {
                        Err(_) => panic!(
                            "Stale token: {:?} is not found in \
                                        the arena. Check code",
                            token
                        ),
                        Ok(curr_node) => {
                            self.node_token = curr_node.$field;
                            Some(token)
                        }
                    },
                }
            }
        }
    };

    // perhaps fold this into the @token branch since this can be implemented with
    // largely the same code with one less Arena::get (one less look-up should
    // translate to more performant code)
    (@node struct $name:ident) => {
        impl<'a, T> Iterator for $name<'a, T> {
            type Item = &'a Node<T>;
            fn next(&mut self) -> Option<&'a Node<T>> {
                match self.token_iter.next() {
                    Some(node_token) => self.token_iter.arena.get(node_token).ok(),
                    None => None,
                }
            }
        }
    };

    (@mut struct $name:ident > $field:ident) => {
        impl<'a, T> Iterator for $name<'a, T> {
            type Item = &'a mut Node<T>;
            fn next(&mut self) -> Option<&'a mut Node<T>> {
                match self.node_token {
                    None => None,
                    Some(curr_node_token) => {
                        let arena = unsafe { self.arena.as_mut().unwrap() };
                        arena.get_mut(curr_node_token).ok().and_then(|curr_node| {
                            self.node_token = curr_node.$field;
                            Some(curr_node)
                        })
                    }
                }
            }
        }

        unsafe impl<T: Sync> Sync for $name<'_, T> {}
        unsafe impl<T: Send> Send for $name<'_, T> {}
    };
}

iterator!(@token struct FollowingSiblingTokens > next_sibling);
iterator!(@token struct PrecedingSiblingTokens > previous_sibling);
iterator!(@token struct ChildrenTokens > next_sibling);
iterator!(@token struct AncestorTokens > parent);
iterator!(@node struct PrecedingSiblings);
iterator!(@node struct FollowingSiblings);
iterator!(@node struct Children);
iterator!(@node struct Ancestors);
iterator!(@mut struct PrecedingSiblingsMut > previous_sibling);
iterator!(@mut struct FollowingSiblingsMut > next_sibling);
iterator!(@mut struct ChildrenMut > next_sibling);
iterator!(@mut struct AncestorsMut > parent);
