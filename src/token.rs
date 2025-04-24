use alloc::collections::VecDeque;
use core::marker::PhantomData;
use core::mem::MaybeUninit;
use core::num::NonZeroUsize;

use crate::arena::Arena;
use crate::iter::*;
use crate::node::Node;
use crate::{Error, Result};

/// A `Token` is a handle to a node in the arena.
#[derive(Clone, Copy, Eq, PartialEq, Debug, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Token {
    pub(crate) index: NonZeroUsize,
}

fn node_operation<T>(
    self_token: Token,
    arena: &mut Arena<T>,
    other_token: Token,
    func: fn(Token, &mut Arena<T>, T) -> Result<Token>,
) -> Result {
    // only a placeholder to get around some trait requirements so I can
    // reuse code. The uninitialized data will be removed so no risk here.
    let dummy_data: T = unsafe { MaybeUninit::zeroed().assume_init() };
    let token = func(self_token, arena, dummy_data)?;
    token.replace_node(arena, other_token)?;
    arena.remove(token)?; // remove uninitialized data
    Ok(())
}

impl Token {
    /// Checks whether a given node is actually a leaf.
    ///
    /// # Panics:
    ///
    /// Panics if the token does not correspond to a node in the arena.
    pub fn is_leaf<T>(self, arena: &Arena<T>) -> Result<bool> {
        arena.get(self).map(|c| c.is_leaf())
    }

    /// Creates a new node with the given data and append to the given node.
    ///
    /// # Panics:
    ///
    /// Panics if the token does not correspond to a node in the arena.
    ///
    /// # Examples:
    ///
    /// ```
    /// use atree::{Arena, Error, iter::TraversalOrder};
    ///
    /// let root_data = "Indo-European";
    /// let (mut arena, root_token) = Arena::with_data(root_data)?;
    ///
    /// let next_node_token = root_token.append(&mut arena, "Germanic")?;
    /// next_node_token.append(&mut arena, "Romance")?;
    /// let mut subtree = root_token.subtree(&arena, TraversalOrder::Pre);
    ///
    /// assert_eq!(subtree.next().unwrap().data, "Indo-European");
    /// assert_eq!(subtree.next().unwrap().data, "Germanic");
    /// assert_eq!(subtree.next().unwrap().data, "Romance");
    /// # Ok::<(), atree::Error>(())
    /// ```
    pub fn append<T>(self, arena: &mut Arena<T>, data: T) -> Result<Token> {
        let new_node_token = arena.allocator.head();
        let previous_sibling = match self.children_mut(arena)?.last() {
            None => {
                // children_mut will have checked indexability so this will not
                // fail
                arena[self].first_child = Some(new_node_token);
                None
            }
            Some(last_child) => {
                last_child.next_sibling = Some(new_node_token);
                Some(last_child.token)
            }
        };

        let node = Node {
            data,
            token: new_node_token,
            parent: Some(self),
            previous_sibling,
            next_sibling: None,
            first_child: None,
        };
        arena.set(new_node_token, node);
        Ok(new_node_token)
    }

    /// Creates a new node with the given data and sets as the previous sibling
    /// of the current node.
    ///
    /// # Panics:
    ///
    /// Panics if the token does not correspond to a node in the arena.
    ///
    /// # Examples:
    ///
    /// ```
    /// use atree::Arena;
    /// use atree::iter::TraversalOrder;
    ///
    /// let root_data = "Indo-European";
    /// let (mut arena, root_token) = Arena::with_data(root_data).unwrap();
    ///
    /// let child2 = root_token.append(&mut arena, "Germanic").unwrap();
    /// let child4 = root_token.append(&mut arena, "Slavic").unwrap();
    /// child2.append(&mut arena, "English").unwrap();
    /// // insert in between children 2 and 4
    /// let child3 = child4.insert_before(&mut arena, "Romance").unwrap();
    /// // insert before child 2
    /// let child1 = child2.insert_before(&mut arena, "Celtic").unwrap();
    ///
    /// let subtree: Vec<_> = root_token
    /// .subtree(&arena, TraversalOrder::Pre)
    /// .map(|x| x.data)
    /// .collect();
    /// assert_eq!(
    /// &[
    /// "Indo-European",
    /// "Celtic",
    /// "Germanic",
    /// "English",
    /// "Romance",
    /// "Slavic"
    /// ],
    /// &subtree[..]
    /// );
    /// ```
    pub fn insert_before<T>(self, arena: &mut Arena<T>, data: T) -> Result<Token> {
        let new_node_token = arena.allocator.head();
        let (self_parent, self_previous_sibling) = match arena.get(self) {
            Ok(node) => (node.parent, node.previous_sibling),
            _ => return Err(Error::TokenNotInArena(self)),
        };
        arena[self].previous_sibling = Some(new_node_token); // already checked
        let previous_sibling = match self_previous_sibling {
            Some(sibling) => match arena.get_mut(sibling) {
                Ok(node) => {
                    node.next_sibling = Some(new_node_token);
                    Ok(Some(sibling))
                }
                _ => Err(Error::CorruptArena),
            },
            None => match self_parent {
                None => Err(Error::CannotInsert),
                Some(p) => match arena.get_mut(p) {
                    Ok(node) => {
                        node.first_child = Some(new_node_token);
                        Ok(None)
                    }
                    _ => Err(Error::CorruptArena),
                },
            },
        }?;

        let node = Node {
            data,
            token: new_node_token,
            parent: self_parent,
            previous_sibling,
            next_sibling: Some(self),
            first_child: None,
        };
        arena.set(new_node_token, node);
        Ok(new_node_token)
    }

    /// Set a node in the arena as the next sibling of the given node. Returns
    /// error if the "other node" is not a root node of a tree (as in it already
    /// has a parent and/or siblings).
    ///
    /// **Note**: for performance reasons, this operation does not check whether
    /// the "self" node is in fact a descendant of the other tree. A cyclic
    /// graph may result.
    ///
    /// # Panics:
    ///
    /// Panics if the token does not correspond to a node in the arena.
    ///
    /// # Examples:
    /// ```
    /// use atree::{Arena, Error, iter::TraversalOrder};
    ///
    /// // root node that we will attach subtrees to
    /// let root_data = "Indo-European";
    /// let (mut arena, root) = Arena::with_data(root_data)?;
    ///
    /// let germanic = root.append(&mut arena, "Germanic")?;
    /// let scots = germanic.append(&mut arena, "German")?;
    /// let english = germanic.append(&mut arena, "English")?;
    ///
    /// let romance = arena.new_node("Romance");
    /// let french = romance.append(&mut arena, "French")?;
    /// let spanish = romance.append(&mut arena, "Spanish")?;
    ///  
    /// germanic.insert_node_after(&mut arena, romance)?;
    ///
    /// let mut iter = root.subtree(&arena, TraversalOrder::Pre).map(|x| x.data);
    /// assert_eq!(iter.next(), Some("Indo-European"));
    /// assert_eq!(iter.next(), Some("Germanic"));
    /// assert_eq!(iter.next(), Some("German"));
    /// assert_eq!(iter.next(), Some("English"));
    /// assert_eq!(iter.next(), Some("Romance"));
    /// assert_eq!(iter.next(), Some("French"));
    /// assert_eq!(iter.next(), Some("Spanish"));
    /// assert!(iter.next().is_none());
    /// # Ok::<(), atree::Error>(())
    /// ```
    pub fn insert_node_after<T>(self, arena: &mut Arena<T>, other: Token) -> Result {
        node_operation(self, arena, other, Token::insert_after)
    }

    /// Set a node in the arena as the previous sibling of the given node.
    /// Returns error if the "other node" is not a root node of a tree (as in it
    /// already has a parent and/or siblings).
    ///
    /// **Note**: for performance reasons, this operation does not check whether
    /// the "self" node is in fact a descendant of the other tree. A cyclic
    /// graph may result.
    ///
    /// # Panics:
    ///
    /// Panics if the token does not correspond to a node in the arena.
    ///
    /// # Examples:
    /// ```
    /// use atree::{Arena, Error, iter::TraversalOrder};
    ///
    /// // root node that we will attach subtrees to
    /// let root_data = "Indo-European";
    /// let (mut arena, root) = Arena::with_data(root_data)?;
    ///
    /// let germanic = root.append(&mut arena, "Germanic")?;
    /// let scots = germanic.append(&mut arena, "German")?;
    /// let english = germanic.append(&mut arena, "English")?;
    ///
    /// let romance = arena.new_node("Romance");
    /// let french = romance.append(&mut arena, "French")?;
    /// let spanish = romance.append(&mut arena, "Spanish")?;
    ///
    /// germanic.insert_node_before(&mut arena, romance)?;
    ///
    /// let mut iter = root.subtree(&arena, TraversalOrder::Pre)
    /// .map(|x| x.data);
    /// assert_eq!(iter.next(), Some("Indo-European"));
    /// assert_eq!(iter.next(), Some("Romance"));
    /// assert_eq!(iter.next(), Some("French"));
    /// assert_eq!(iter.next(), Some("Spanish"));
    /// assert_eq!(iter.next(), Some("Germanic"));
    /// assert_eq!(iter.next(), Some("German"));
    /// assert_eq!(iter.next(), Some("English"));
    /// assert!(iter.next().is_none());
    /// # Ok::<(), atree::Error>(())
    /// ```
    pub fn insert_node_before<T>(self, arena: &mut Arena<T>, other: Token) -> Result {
        node_operation(self, arena, other, Token::insert_before)
    }

    /// Creates a new node with the given data and sets as the next sibling of
    /// the current node.
    ///
    /// # Panics:
    ///
    /// Panics if the token does not correspond to a node in the arena.
    ///
    /// # Examples:
    ///
    /// ```
    /// use atree::{Arena, Error, iter::TraversalOrder};
    ///
    /// let root_data = "Indo-European";
    /// let (mut arena, root_token) = Arena::with_data(root_data)?;
    ///
    /// let child1 = root_token.append(&mut arena, "Romance")?;
    /// let child3 = root_token.append(&mut arena, "Germanic")?;
    /// child1.append(&mut arena, "French")?;
    /// // insert betwern children 1 and 4
    /// let child2 = child1.insert_after(&mut arena, "Celtic")?;
    /// // insert after child 3
    /// child3.insert_after(&mut arena, "Slavic")?;
    ///
    /// let subtree: Vec<_> = root_token
    /// .subtree(&arena, TraversalOrder::Pre)
    /// .map(|x| x.data)
    /// .collect();
    /// assert_eq!(
    /// &[
    /// "Indo-European",
    /// "Romance",
    /// "French",
    /// "Celtic",
    /// "Germanic",
    /// "Slavic"
    /// ],
    /// &subtree[..]
    /// );
    /// # Ok::<(), atree::Error>(())
    /// ```
    pub fn insert_after<T>(self, arena: &mut Arena<T>, data: T) -> Result<Token> {
        let new_node_token = arena.allocator.head();
        let (self_parent, self_next_sibling) = arena
            .get(self)
            .map(|node| (node.parent, node.next_sibling))?;

        arena[self].next_sibling = Some(new_node_token); // already checked
        let next_sibling = match self_next_sibling {
            None => None,
            Some(sibling) => match arena.get_mut(sibling) {
                Ok(node) => {
                    node.previous_sibling = Some(new_node_token);
                    Some(sibling)
                }
                _ => return Err(Error::CorruptArena),
            },
        };

        let node = Node {
            data,
            token: new_node_token,
            parent: self_parent,
            previous_sibling: Some(self),
            next_sibling,
            first_child: None,
        };
        arena.set(new_node_token, node);
        Ok(new_node_token)
    }

    /// Attaches a different tree in the arena to a node. Returns error if the
    /// "root node" of the other tree is not really a root node (as in it
    /// already has a parent and/or siblings). To attach a tree from a different
    /// arena, use [`copy_and_append_subtree`] instead.
    ///
    /// **Note**: for performance reasons, this operation does not check whether
    /// the "self" node is in fact a descendant of the other tree. A cyclic
    /// graph may result.
    ///
    /// # Panics:
    ///
    /// Panics if the token does not correspond to a node in the arena.
    ///
    /// # Examples:
    /// ```
    /// use atree::{Arena, Error, iter::TraversalOrder};
    ///
    /// // root node that we will attach subtrees to
    /// let root_data = "Indo-European";
    /// let (mut arena, root) = Arena::with_data(root_data)?;
    ///
    /// // the Germanic branch
    /// let germanic = arena.new_node("Germanic");
    /// let west = germanic.append(&mut arena, "West")?;
    /// let scots = west.append(&mut arena, "Scots")?;
    /// let english = west.append(&mut arena, "English")?;
    ///
    /// // the Romance branch
    /// let romance = arena.new_node("Romance");
    /// let french = romance.append(&mut arena, "French")?;
    /// let italian = romance.append(&mut arena, "Italian")?;
    ///
    /// // attach subtrees
    /// root.append_node(&mut arena, romance)?;
    /// root.append_node(&mut arena, germanic)?;
    ///
    /// let mut iter = root.subtree(&arena, TraversalOrder::Pre).map(|x| x.data);
    /// assert_eq!(iter.next(), Some("Indo-European"));
    /// assert_eq!(iter.next(), Some("Romance"));
    /// assert_eq!(iter.next(), Some("French"));
    /// assert_eq!(iter.next(), Some("Italian"));
    /// assert_eq!(iter.next(), Some("Germanic"));
    /// assert_eq!(iter.next(), Some("West"));
    /// assert_eq!(iter.next(), Some("Scots"));
    /// assert_eq!(iter.next(), Some("English"));
    /// assert!(iter.next().is_none());
    /// # Ok::<(), atree::Error>(())
    /// ```
    ///
    /// [`copy_and_append_subtree`]: struct.Arena.html#method.copy_and_append_subtree
    pub fn append_node<T>(self, arena: &mut Arena<T>, other: Self) -> Result {
        node_operation(self, arena, other, Token::append)
    }

    /// Detaches the given node and its descendants into its own tree while
    /// keeping it in the same arena. To detach and allocate the subtree into its
    /// own arena, use [`split_at`] instead.
    ///
    /// # Panics:
    ///
    /// Panics if the token does not correspond to a node in the arena.
    ///
    /// # Examples:
    /// ```
    /// use atree::{Arena, Error, iter::TraversalOrder};
    ///
    /// // root node that we will attach subtrees to
    /// let root_data = "Indo-European";
    /// let (mut arena, root) = Arena::with_data(root_data)?;
    ///
    /// // the Germanic branch
    /// let germanic = root.append(&mut arena, "Germanic")?;
    /// let west = germanic.append(&mut arena, "West")?;
    /// let scots = west.append(&mut arena, "Scots")?;
    /// let english = west.append(&mut arena, "English")?;
    ///
    /// // detach the west branch from the main tree
    /// west.detach(&mut arena);
    ///
    /// // the west branch is gone from the original tree
    /// let mut iter = root.subtree(&arena, TraversalOrder::Pre).map(|x| x.data);
    /// assert_eq!(iter.next(), Some("Indo-European"));
    /// assert_eq!(iter.next(), Some("Germanic"));
    /// assert!(iter.next().is_none());
    ///
    /// // it exists on its own
    /// let mut iter = west.subtree(&arena, TraversalOrder::Pre).map(|x| x.data);
    /// assert_eq!(iter.next(), Some("West"));
    /// assert_eq!(iter.next(), Some("Scots"));
    /// assert_eq!(iter.next(), Some("English"));
    /// assert!(iter.next().is_none());
    /// # Ok::<(), atree::Error>(())
    /// ```
    ///
    /// [`split_at`]: struct.Arena.html#method.split_at
    pub fn detach<T>(self, arena: &mut Arena<T>) -> Result {
        let (parent, previous_sibling, next_sibling) = arena.get_mut(self).map(|node| {
            let parent = node.parent;
            let previous_sibling = node.previous_sibling;
            let next_sibling = node.next_sibling;
            node.parent = None;
            node.previous_sibling = None;
            node.next_sibling = None;
            (parent, previous_sibling, next_sibling)
        })?;

        match previous_sibling {
            Some(token) => match arena.get_mut(token) {
                Ok(node) => node.next_sibling = next_sibling,
                _ => return Err(Error::CorruptArena),
            },
            None => {
                if let Some(token) = parent {
                    match arena.get_mut(token) {
                        Ok(n) => n.first_child = next_sibling,
                        _ => return Err(Error::CorruptArena),
                    }
                }
            }
        }

        if let Some(token) = next_sibling {
            match arena.get_mut(token) {
                Ok(node) => node.previous_sibling = previous_sibling,
                _ => return Err(Error::CorruptArena),
            }
        }
        Ok(())
    }

    /// Replace the subtree of self with the subtree of other. Does not remove
    /// self or its descendants but simply makes it a standalone tree within the
    /// arena.
    ///
    /// **Note**: for performance reasons, this operation does not check whether
    /// the "other" node is in fact a descendant of the parent tree of self. A
    /// cyclic graph may result.
    ///
    /// # Panics:
    ///
    /// Panics if the token does not correspond to a node in the arena.
    ///
    /// # Examples:
    /// ```
    /// use atree::Arena;
    /// use atree::iter::TraversalOrder;
    ///
    /// // root node that we will attach subtrees to
    /// let root_data = "Indo-European";
    /// let (mut arena, root) = Arena::with_data(root_data).unwrap();
    ///
    /// // the Germanic branch
    /// let germanic = root.append(&mut arena, "Germanic").unwrap();
    /// let west = germanic.append(&mut arena, "West").unwrap();
    /// let scots = west.append(&mut arena, "Scots").unwrap();
    /// let english = west.append(&mut arena, "English").unwrap();
    ///
    /// // the slavic branch
    /// let slavic = root.append(&mut arena, "Slavic").unwrap();
    /// let polish = slavic.append(&mut arena, "Polish").unwrap();
    /// let russian = slavic.append(&mut arena, "Russian").unwrap();
    ///
    /// // the Romance branch
    /// let romance = arena.new_node("Romance");
    /// let french = romance.append(&mut arena, "French").unwrap();
    /// let italian = romance.append(&mut arena, "Italian").unwrap();
    ///
    /// // replace_node germanic with romance
    /// germanic.replace_node(&mut arena, romance).unwrap();
    ///
    /// let mut iter = root.subtree(&arena, TraversalOrder::Pre).map(|x| x.data);
    /// assert_eq!(iter.next(), Some("Indo-European"));
    /// assert_eq!(iter.next(), Some("Romance"));
    /// assert_eq!(iter.next(), Some("French"));
    /// assert_eq!(iter.next(), Some("Italian"));
    /// assert_eq!(iter.next(), Some("Slavic"));
    /// assert_eq!(iter.next(), Some("Polish"));
    /// assert_eq!(iter.next(), Some("Russian"));
    /// assert!(iter.next().is_none());
    /// ```
    pub fn replace_node<T>(self, arena: &mut Arena<T>, other: Token) -> Result {
        let self_node = arena.get(self)?;
        let parent = self_node.parent;
        let previous_sibling = self_node.previous_sibling;
        let next_sibling = self_node.next_sibling;

        let other_node = arena.get_mut(other)?;

        // check that the other node is really a root node of its own
        match (
            other_node.previous_sibling,
            other_node.next_sibling,
            other_node.parent,
        ) {
            (None, None, None) => (),
            _ => return Err(Error::NotARootNode),
        }

        // replace_node the self node with the other node
        other_node.parent = parent;
        other_node.next_sibling = next_sibling;
        other_node.previous_sibling = previous_sibling;

        let self_node = &mut arena[self]; // indexability has been checked
        self_node.parent = None;
        self_node.previous_sibling = None;
        self_node.next_sibling = None;

        // update previous_sibling, next_sibling and parent of the self node
        match previous_sibling {
            Some(sibling) => match arena.get_mut(sibling) {
                Ok(node) => node.next_sibling = Some(other),
                _ => return Err(Error::CorruptArena),
            },
            None => {
                if let Some(p) = parent {
                    match arena.get_mut(p) {
                        Ok(node) => node.first_child = Some(other),
                        _ => return Err(Error::CorruptArena),
                    }
                }
            }
        }

        if let Some(sibling) = next_sibling {
            match arena.get_mut(sibling) {
                Ok(node) => node.previous_sibling = Some(other),
                _ => return Err(Error::CorruptArena),
            }
        }

        Ok(())
    }

    /// Returns an iterator of tokens of ancestor nodes.
    ///
    /// # Panics:
    ///
    /// Panics if the token does not correspond to a node in the arena.
    ///
    /// # Examples:
    ///
    /// ```
    /// use atree::Arena;
    ///
    /// let root_data = "Indo-European";
    /// let (mut arena, root_token) = Arena::with_data(root_data)?;
    ///
    /// let child_token = root_token.append(&mut arena, "Germanic")?;
    /// let grandchild_token = child_token.append(&mut arena, "English")?;
    /// let mut ancestors_tokens = grandchild_token.ancestors_tokens(&arena)?;
    ///
    /// assert_eq!(ancestors_tokens.next(), Some(child_token));
    /// assert_eq!(ancestors_tokens.next(), Some(root_token));
    /// assert!(ancestors_tokens.next().is_none());
    /// # Ok::<(), atree::Error>(())
    /// ```
    pub fn ancestors_tokens<'a, T>(self, arena: &'a Arena<T>) -> Result<AncestorTokens<'a, T>> {
        let parent = arena.get(self)?.parent;
        Ok(AncestorTokens {
            arena,
            node_token: parent,
        })
    }

    /// Returns an iterator of tokens of siblings preceding the current node.
    ///
    /// # Panics:
    ///
    /// Panics if the token does not correspond to a node in the arena.
    ///
    /// # Examples:
    ///
    /// ```
    /// use atree::Arena;
    ///
    /// let root_data = "Indo-European";
    /// let (mut arena, root_token) = Arena::with_data(root_data).unwrap();
    ///
    /// let first_child_token = root_token.append(&mut arena, "Germanic").unwrap();
    /// let second_child_token = root_token.append(&mut arena, "Romance").unwrap();
    /// let third_child_token = root_token.append(&mut arena, "Slavic").unwrap();
    /// root_token.append(&mut arena, "Hellenic").unwrap();
    ///
    /// let mut sibling_tokens = third_child_token.preceding_siblings_tokens(&arena).unwrap();
    /// assert_eq!(sibling_tokens.next(), Some(second_child_token));
    /// assert_eq!(sibling_tokens.next(), Some(first_child_token));
    /// assert!(sibling_tokens.next().is_none());
    /// ```
    pub fn preceding_siblings_tokens<'a, T>(
        self,
        arena: &'a Arena<T>,
    ) -> Result<PrecedingSiblingTokens<'a, T>> {
        let previous_sibling = arena.get(self)?.previous_sibling;
        Ok(PrecedingSiblingTokens {
            arena,
            node_token: previous_sibling,
        })
    }

    /// Returns an iterator of tokens of siblings following the current node.
    ///
    /// # Panics:
    ///
    /// Panics if the token does not correspond to a node in the arena.
    ///
    /// # Examples:
    ///
    /// ```
    /// use atree::Arena;
    ///
    /// let root_data = "Indo-European";
    /// let (mut arena, root_token) = Arena::with_data(root_data)?;
    ///
    /// root_token.append(&mut arena, "Romance")?;
    /// let second_child_token = root_token.append(&mut arena, "Germanic")?;
    /// let third_child_token = root_token.append(&mut arena, "Slavic")?;
    /// let fourth_child_token = root_token.append(&mut arena, "Hellenic")?;
    ///
    /// let mut sibling_tokens = second_child_token.following_siblings_tokens(&arena)?;
    /// assert_eq!(sibling_tokens.next(), Some(third_child_token));
    /// assert_eq!(sibling_tokens.next(), Some(fourth_child_token));
    /// assert!(sibling_tokens.next().is_none());
    /// # Ok::<(), atree::Error>(())
    /// ```
    pub fn following_siblings_tokens<'a, T>(
        self,
        arena: &'a Arena<T>,
    ) -> Result<FollowingSiblingTokens<'a, T>> {
        let next_sibling = arena.get(self)?.next_sibling;
        Ok(FollowingSiblingTokens {
            arena,
            node_token: next_sibling,
        })
    }

    /// Returns an iterator of tokens of child nodes in the order of insertion.
    ///
    /// # Panics:
    ///
    /// Panics if the token does not correspond to a node in the arena.
    ///
    /// # Examples:
    ///
    /// ```
    /// use atree::Arena;
    ///
    /// let root_data = "Indo-European";
    /// let (mut arena, root_token) = Arena::with_data(root_data)?;
    ///
    /// let first_child_token = root_token.append(&mut arena, "Romance")?;
    /// let second_child_token = root_token.append(&mut arena, "Germanic")?;
    /// let third_child_token = root_token.append(&mut arena, "Slavic")?;
    /// let fourth_child_token = root_token.append(&mut arena, "Hellenic")?;
    ///
    /// let mut children_tokens = root_token.children_tokens(&arena)?;
    /// assert_eq!(children_tokens.next(), Some(first_child_token));
    /// assert_eq!(children_tokens.next(), Some(second_child_token));
    /// assert_eq!(children_tokens.next(), Some(third_child_token));
    /// assert_eq!(children_tokens.next(), Some(fourth_child_token));
    /// assert!(children_tokens.next().is_none());
    /// # Ok::<(), atree::Error>(())
    /// ```
    pub fn children_tokens<'a, T>(self, arena: &'a Arena<T>) -> Result<ChildrenTokens<'a, T>> {
        let first_child = arena.get(self)?.first_child;
        Ok(ChildrenTokens {
            arena,
            node_token: first_child,
        })
    }

    /// Returns an iterator of references of ancestor nodes.
    ///
    /// # Panics:
    ///
    /// Panics if the token does not correspond to a node in the arena.
    ///
    /// # Examples:
    ///
    /// ```
    /// use atree::Arena;
    ///
    /// let root_data = "Indo-European";
    /// let (mut arena, root_token) = Arena::with_data(root_data)?;
    ///
    /// let child_token = root_token.append(&mut arena, "Germanic")?;
    /// let grandchild_token = child_token.append(&mut arena, "Swedish")?;
    /// let mut ancestors = grandchild_token.ancestors(&arena)?;
    ///
    /// assert_eq!(ancestors.next().unwrap().data, "Germanic");
    /// assert_eq!(ancestors.next().unwrap().data, "Indo-European");
    /// assert!(ancestors.next().is_none());
    /// # Ok::<(), atree::Error>(())
    /// ```
    pub fn ancestors<'a, T>(self, arena: &'a Arena<T>) -> Result<Ancestors<'a, T>> {
        Ok(Ancestors {
            token_iter: self.ancestors_tokens(arena)?,
        })
    }

    /// Returns an iterator of references of sibling nodes preceding the current
    /// node.
    ///
    /// # Panics:
    ///
    /// Panics if the token does not correspond to a node in the arena.
    ///
    /// # Examples:
    ///
    /// ```
    /// use atree::Arena;
    ///
    /// let root_data = "Indo-European";
    /// let (mut arena, root_token) = Arena::with_data(root_data)?;
    ///
    /// root_token.append(&mut arena, "Romance")?;
    /// root_token.append(&mut arena, "Germanic")?;
    /// let third_child_token = root_token.append(&mut arena, "Slavic")?;
    /// root_token.append(&mut arena, "Celtic")?;
    ///
    /// let mut siblings = third_child_token.preceding_siblings(&arena)?;
    /// assert_eq!(siblings.next().unwrap().data, "Germanic");
    /// assert_eq!(siblings.next().unwrap().data, "Romance");
    /// assert!(siblings.next().is_none());
    /// # Ok::<(), atree::Error>(())
    /// ```
    pub fn preceding_siblings<'a, T>(
        self,
        arena: &'a Arena<T>,
    ) -> Result<PrecedingSiblings<'a, T>> {
        Ok(PrecedingSiblings {
            token_iter: self.preceding_siblings_tokens(arena)?,
        })
    }

    /// Returns an iterator of references of sibling nodes following the current
    /// node.
    ///
    /// # Panics:
    ///
    /// Panics if the token does not correspond to a node in the arena.
    ///
    /// # Examples:
    ///
    /// ```
    /// use atree::Arena;
    ///
    /// let root_data = "Indo-European";
    /// let (mut arena, root_token) = Arena::with_data(root_data)?;
    ///
    /// root_token.append(&mut arena, "Romance")?;
    /// let second_child_token = root_token.append(&mut arena, "Germanic")?;
    /// root_token.append(&mut arena, "Slavic")?;
    /// root_token.append(&mut arena, "Hellenic")?;
    ///
    /// let mut siblings = second_child_token.following_siblings(&arena)?;
    /// assert_eq!(siblings.next().unwrap().data, "Slavic");
    /// assert_eq!(siblings.next().unwrap().data, "Hellenic");
    /// assert!(siblings.next().is_none());
    /// # Ok::<(), atree::Error>(())
    /// ```
    pub fn following_siblings<'a, T>(
        self,
        arena: &'a Arena<T>,
    ) -> Result<FollowingSiblings<'a, T>> {
        Ok(FollowingSiblings {
            token_iter: self.following_siblings_tokens(arena)?,
        })
    }

    /// Returns an iterator of child node references in the order of insertion.
    ///
    /// # Panics:
    ///
    /// Panics if the token does not correspond to a node in the arena.
    ///
    /// # Examples:
    ///
    /// ```
    /// use atree::Arena;
    ///
    /// let root_data = "Indo-European";
    /// let (mut arena, root_token) = Arena::with_data(root_data)?;
    ///
    /// let first_child_token = root_token.append(&mut arena, "Germanic")?;
    /// let second_child_token = root_token.append(&mut arena, "Romance")?;
    /// let third_child_token = root_token.append(&mut arena, "Slavic")?;
    /// let fourth_child_token = root_token.append(&mut arena, "Celtic")?;
    ///
    /// let mut children = root_token.children(&arena)?;
    /// assert_eq!(children.next().unwrap().data, "Germanic");
    /// assert_eq!(children.next().unwrap().data, "Romance");
    /// assert_eq!(children.next().unwrap().data, "Slavic");
    /// assert_eq!(children.next().unwrap().data, "Celtic");
    /// assert!(children.next().is_none());
    /// # Ok::<(), atree::Error>(())
    /// ```
    pub fn children<'a, T>(self, arena: &'a Arena<T>) -> Result<Children<'a, T>> {
        Ok(Children {
            token_iter: self.children_tokens(arena)?,
        })
    }

    /// Returns an iterator of mutable ancestor node references.
    ///
    /// # Panics:
    ///
    /// Panics if the token does not correspond to a node in the arena.
    ///
    /// # Examples:
    ///
    /// ```
    /// use atree::Arena;
    ///
    /// let root_data = 1usize;
    /// let (mut arena, root_token) = Arena::with_data(root_data)?;
    ///
    /// let child_token = root_token.append(&mut arena, 2usize)?;
    /// let grandchild_token = child_token.append(&mut arena, 3usize)?;
    /// let great_grandchild_token = grandchild_token.append(&mut arena, 4usize)?;
    /// let ggreat_grandchild_token = great_grandchild_token.append(&mut arena, 5usize)?;
    ///
    /// for x in ggreat_grandchild_token.ancestors_mut(&mut arena) {
    ///     x.data += 2;
    /// }
    ///
    /// let mut ancestors = ggreat_grandchild_token.ancestors(&arena)?;
    /// assert_eq!(ancestors.next().unwrap().data, 6usize);
    /// assert_eq!(ancestors.next().unwrap().data, 5usize);
    /// assert_eq!(ancestors.next().unwrap().data, 4usize);
    /// assert_eq!(ancestors.next().unwrap().data, 3usize);
    /// assert!(ancestors.next().is_none());
    /// # Ok::<(), atree::Error>(())
    /// ```
    pub fn ancestors_mut<'a, T>(self, arena: &'a mut Arena<T>) -> AncestorsMut<'a, T> {
        AncestorsMut {
            arena: arena as *mut Arena<T>,
            node_token: Some(self),
            marker: PhantomData,
        }
    }

    /// Returns an iterator of mutable references of sibling nodes that follow
    /// the current node.
    ///
    /// # Panics:
    ///
    /// Panics if the token does not correspond to a node in the arena.
    ///
    /// # Examples:
    ///
    /// ```
    /// use atree::Arena;
    ///
    /// let root_data = 1usize;
    /// let (mut arena, root_token) = Arena::with_data(root_data)?;
    ///
    /// root_token.append(&mut arena, 2usize)?;
    /// let second_child_token = root_token.append(&mut arena, 3usize)?;
    /// root_token.append(&mut arena, 4usize)?;
    /// root_token.append(&mut arena, 5usize)?;
    ///
    /// for x in second_child_token.following_siblings_mut(&mut arena)? {
    ///     x.data += 2;
    /// }
    ///
    /// let mut children = root_token.children(&arena)?;
    /// assert_eq!(children.next().unwrap().data, 2usize);
    /// assert_eq!(children.next().unwrap().data, 3usize);
    /// assert_eq!(children.next().unwrap().data, 6usize);
    /// assert_eq!(children.next().unwrap().data, 7usize);
    /// assert!(children.next().is_none());
    /// # Ok::<(), atree::Error>(())
    /// ```
    pub fn following_siblings_mut<'a, T>(
        self,
        arena: &'a mut Arena<T>,
    ) -> Result<FollowingSiblingsMut<'a, T>> {
        let next_sibling = arena.get(self)?.next_sibling;
        Ok(FollowingSiblingsMut {
            arena: arena as *mut Arena<T>,
            node_token: next_sibling,
            marker: PhantomData,
        })
    }

    /// Returns an iterator of mutable references of sibling nodes that precede
    /// the current node.
    ///
    /// # Panics:
    ///
    /// Panics if the token does not correspond to a node in the arena.
    ///
    /// # Examples:
    ///
    /// ```
    /// use atree::Arena;
    ///
    /// let root_data = 1usize;
    /// let (mut arena, root_token) = Arena::with_data(root_data)?;
    ///
    /// root_token.append(&mut arena, 2usize)?;
    /// root_token.append(&mut arena, 3usize)?;
    /// root_token.append(&mut arena, 4usize)?;
    /// let fourth_child_token = root_token.append(&mut arena, 5usize)?;
    ///
    /// for x in fourth_child_token.preceding_siblings_mut(&mut arena)? {
    ///     x.data += 5;
    /// }
    ///
    /// let mut children = root_token.children(&arena)?;
    /// assert_eq!(children.next().unwrap().data, 7usize);
    /// assert_eq!(children.next().unwrap().data, 8usize);
    /// assert_eq!(children.next().unwrap().data, 9usize);
    /// assert_eq!(children.next().unwrap().data, 5usize);
    /// assert!(children.next().is_none());
    /// # Ok::<(), atree::Error>(())
    /// ```
    pub fn preceding_siblings_mut<'a, T>(
        self,
        arena: &'a mut Arena<T>,
    ) -> Result<PrecedingSiblingsMut<'a, T>> {
        let previous_sibling = arena.get(self)?.previous_sibling;
        Ok(PrecedingSiblingsMut {
            arena: arena as *mut Arena<T>,
            node_token: previous_sibling,
            marker: PhantomData,
        })
    }

    /// Returns an iterator of mutable references of child nodes in the order of
    /// insertion.
    ///
    /// # Panics:
    ///
    /// Panics if the token does not correspond to a node in the arena.
    ///
    /// # Examples:
    ///
    /// ```
    /// use atree::Arena;
    ///
    /// let root_data = 1usize;
    /// let (mut arena, root_token) = Arena::with_data(root_data)?;
    ///
    /// root_token.append(&mut arena, 2usize)?;
    /// root_token.append(&mut arena, 3usize)?;
    /// let third_child_token = root_token.append(&mut arena, 4usize)?;
    /// root_token.append(&mut arena, 5usize)?;
    /// let grandchild = third_child_token.append(&mut arena, 10usize)?;
    ///
    /// for x in root_token.children_mut(&mut arena)? {
    ///     x.data += 10;
    /// }
    ///
    /// let mut children = root_token.children(&arena)?;
    /// assert_eq!(children.next().unwrap().data, 12);
    /// assert_eq!(children.next().unwrap().data, 13);
    /// assert_eq!(children.next().unwrap().data, 14);
    /// assert_eq!(children.next().unwrap().data, 15);
    /// assert_eq!(arena.get(grandchild).unwrap().data, 10);
    /// assert!(children.next().is_none());
    /// # Ok::<(), atree::Error>(())
    /// ```
    pub fn children_mut<'a, T>(self, arena: &'a mut Arena<T>) -> Result<ChildrenMut<'a, T>> {
        let first_child = arena.get(self)?.first_child;
        Ok(ChildrenMut {
            arena: arena as *mut Arena<T>,
            node_token: first_child,
            marker: PhantomData,
        })
    }

    /// Returns an iterator of tokens of subtree nodes of the given node.
    ///
    /// # Panics:
    ///
    /// Panics if the token does not correspond to a node in the arena.
    ///
    /// # Examples:
    ///
    /// ```
    /// use atree::{Arena, Error, iter::TraversalOrder};
    ///
    /// let root_data = "Indo-European";
    /// let (mut arena, root_token) = Arena::with_data(root_data)?;
    ///
    /// let first_child = root_token.append(&mut arena, "Romance")?;
    /// let second_child = root_token.append(&mut arena, "Germanic")?;
    /// let third_child = root_token.append(&mut arena, "Slavic")?;
    /// let first_grandchild = second_child.append(&mut arena, "English")?;
    /// let second_grandchild = second_child.append(&mut arena, "Icelandic")?;
    /// let fourth_child = root_token.append(&mut arena, "Celtic")?;
    ///
    /// let mut subtree = root_token.subtree_tokens(&arena, TraversalOrder::Pre);
    /// assert_eq!(subtree.next(), Some(root_token));
    /// assert_eq!(subtree.next(), Some(first_child));
    /// assert_eq!(subtree.next(), Some(second_child));
    /// assert_eq!(subtree.next(), Some(first_grandchild));
    /// assert_eq!(subtree.next(), Some(second_grandchild));
    /// assert_eq!(subtree.next(), Some(third_child));
    /// assert_eq!(subtree.next(), Some(fourth_child));
    /// assert!(subtree.next().is_none());
    ///
    /// let mut subtree = second_grandchild.subtree_tokens(&arena, TraversalOrder::Pre);
    /// assert_eq!(subtree.next(), Some(second_grandchild));
    /// assert!(subtree.next().is_none());
    /// # Ok::<(), atree::Error>(())
    /// ```
    pub fn subtree_tokens<'a, T>(
        self,
        arena: &'a Arena<T>,
        order: TraversalOrder,
    ) -> SubtreeTokens<'a, T> {
        let preord_tokens_next =
            |iter: &mut SubtreeTokens<'a, T>| depth_first_tokens_next(iter, preorder_next);
        let postord_tokens_next =
            |iter: &mut SubtreeTokens<'a, T>| depth_first_tokens_next(iter, postorder_next);
        match order {
            TraversalOrder::Pre => SubtreeTokens {
                arena,
                subtree_root: self,
                node_token: Some(self),
                branch: Branch::Child,
                curr_level: VecDeque::new(), // unused field
                next_level: VecDeque::new(), // unused field
                next: preord_tokens_next,
            },
            TraversalOrder::Post => {
                let (node_token, branch) = postorder_next(self, self, Branch::Child, arena)
                    .expect("postorder_next should not return None");
                SubtreeTokens {
                    arena,
                    subtree_root: self,
                    node_token,
                    branch,
                    curr_level: VecDeque::new(), // unused field
                    next_level: VecDeque::new(), // unused field
                    next: postord_tokens_next,
                }
            }
            TraversalOrder::Level => {
                SubtreeTokens {
                    arena,
                    subtree_root: self,   // unused field
                    node_token: None,     // unused field
                    branch: Branch::None, // unused field
                    curr_level: core::iter::once(self).collect(),
                    next_level: VecDeque::new(),
                    next: breadth_first_tokens_next,
                }
            }
        }
    }

    /// Returns an iterator of references of subtree nodes of the given node.
    ///
    /// # Panics:
    ///
    /// Panics if the token does not correspond to a node in the arena.
    ///
    /// # Examples:
    ///
    /// ```
    /// use atree::{Arena, Error, iter::TraversalOrder};
    ///
    /// let root_data = "Indo-European";
    /// let (mut arena, root_token) = Arena::with_data(root_data)?;
    ///
    /// root_token.append(&mut arena, "Romance")?;
    /// root_token.append(&mut arena, "Germanic")?;
    /// let third_child = root_token.append(&mut arena, "Slavic")?;
    /// root_token.append(&mut arena, "Celtic")?;
    /// third_child.append(&mut arena, "Polish")?;
    /// third_child.append(&mut arena, "Slovakian")?;
    ///
    /// let mut subtree = root_token.subtree(&arena, TraversalOrder::Pre);
    /// assert_eq!(subtree.next().unwrap().data, "Indo-European");
    /// assert_eq!(subtree.next().unwrap().data, "Romance");
    /// assert_eq!(subtree.next().unwrap().data, "Germanic");
    /// assert_eq!(subtree.next().unwrap().data, "Slavic");
    /// assert_eq!(subtree.next().unwrap().data, "Polish");
    /// assert_eq!(subtree.next().unwrap().data, "Slovakian");
    /// assert_eq!(subtree.next().unwrap().data, "Celtic");
    /// assert!(subtree.next().is_none());
    /// # Ok::<(), atree::Error>(())
    /// ```
    pub fn subtree<'a, T>(self, arena: &'a Arena<T>, order: TraversalOrder) -> Subtree<'a, T> {
        Subtree {
            arena,
            iter: self.subtree_tokens(arena, order),
        }
    }

    /// Returns an iterator of mutable references of subtree nodes of the given
    /// node.
    ///
    /// # Panics:
    ///
    /// Panics if the token does not correspond to a node in the arena.
    ///
    /// # Examples:
    ///
    /// ```
    /// use atree::{Arena, Error, iter::TraversalOrder};
    ///
    /// let root_data = 1usize;
    /// let (mut arena, root_token) = Arena::with_data(root_data)?;
    ///
    /// root_token.append(&mut arena, 2usize)?;
    /// root_token.append(&mut arena, 3usize)?;
    /// let third_child = root_token.append(&mut arena, 4usize)?;
    /// root_token.append(&mut arena, 5usize)?;
    /// third_child.append(&mut arena, 10usize)?;
    /// third_child.append(&mut arena, 20usize)?;
    ///
    /// for x in root_token.subtree_mut(&mut arena, TraversalOrder::Pre) {
    ///     x.data += 100;
    /// }
    ///
    /// let mut subtree = root_token.subtree(&arena, TraversalOrder::Pre);
    /// assert_eq!(subtree.next().unwrap().data, 101);
    /// assert_eq!(subtree.next().unwrap().data, 102);
    /// assert_eq!(subtree.next().unwrap().data, 103);
    /// assert_eq!(subtree.next().unwrap().data, 104);
    /// assert_eq!(subtree.next().unwrap().data, 110);
    /// assert_eq!(subtree.next().unwrap().data, 120);
    /// assert_eq!(subtree.next().unwrap().data, 105);
    /// assert!(subtree.next().is_none());
    /// # Ok::<(), atree::Error>(())
    /// ```
    pub fn subtree_mut<'a, T>(
        self,
        arena: &'a mut Arena<T>,
        order: TraversalOrder,
    ) -> SubtreeMut<'a, T> {
        SubtreeMut {
            arena: arena as *mut Arena<T>,
            iter: self.subtree_tokens(arena, order),
            marker: PhantomData,
        }
    }

    /// Removes all descendants of the current node.
    pub(crate) fn remove_descendants<T>(self, arena: &mut Arena<T>) {
        // This will not silently fail since postorder_next will panic if self
        // isn't valid.  This won't do anything if self has no descendants, but
        // that's the intended behavior.
        if let Ok((Some(mut token), mut branch)) = postorder_next(self, self, Branch::Child, arena)
        {
            while branch != Branch::None {
                if let Ok((t, b)) = postorder_next(token, self, branch, arena) {
                    arena.allocator.remove(token); // should not fail (not here anyway)
                    token = t.expect("postorder_next should not return None");
                    branch = b;
                }
            }
            arena[self].first_child = None;
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    #[allow(clippy::cognitive_complexity)]
    fn replace_node() {
        let closure = move || {
            // root node that we will attach subtrees to
            let root_data = "Indo-European";
            let (mut arena, root) = Arena::with_data(root_data)?;

            // the Germanic branch
            let germanic = root.append(&mut arena, "Germanic")?;
            let west = germanic.append(&mut arena, "West")?;
            west.append(&mut arena, "Scots")?;
            west.append(&mut arena, "English")?;

            // the slavic branch
            let slavic = root.append(&mut arena, "Slavic")?;
            slavic.append(&mut arena, "Polish")?;
            slavic.append(&mut arena, "Russian")?;

            let mut iter = root.subtree(&arena, TraversalOrder::Pre).map(|x| x.data);
            assert_eq!(iter.next(), Some("Indo-European"));
            assert_eq!(iter.next(), Some("Germanic"));
            assert_eq!(iter.next(), Some("West"));
            assert_eq!(iter.next(), Some("Scots"));
            assert_eq!(iter.next(), Some("English"));
            assert_eq!(iter.next(), Some("Slavic"));
            assert_eq!(iter.next(), Some("Polish"));
            assert_eq!(iter.next(), Some("Russian"));
            assert!(iter.next().is_none());

            // the Romance branch
            let romance = arena.new_node("Romance");
            romance.append(&mut arena, "French")?;
            romance.append(&mut arena, "Italian")?;

            // replace_node germanic with romance
            germanic.replace_node(&mut arena, romance)?;

            let mut iter = root.subtree(&arena, TraversalOrder::Pre).map(|x| x.data);
            assert_eq!(iter.next(), Some("Indo-European"));
            assert_eq!(iter.next(), Some("Romance"));
            assert_eq!(iter.next(), Some("French"));
            assert_eq!(iter.next(), Some("Italian"));
            assert_eq!(iter.next(), Some("Slavic"));
            assert_eq!(iter.next(), Some("Polish"));
            assert_eq!(iter.next(), Some("Russian"));
            assert!(iter.next().is_none());

            // How about the other way around (replacing the slavic branch instead
            slavic.replace_node(&mut arena, germanic)?;

            let mut iter = root.subtree(&arena, TraversalOrder::Pre).map(|x| x.data);
            assert_eq!(iter.next(), Some("Indo-European"));
            assert_eq!(iter.next(), Some("Romance"));
            assert_eq!(iter.next(), Some("French"));
            assert_eq!(iter.next(), Some("Italian"));
            assert_eq!(iter.next(), Some("Germanic"));
            assert_eq!(iter.next(), Some("West"));
            assert_eq!(iter.next(), Some("Scots"));
            assert_eq!(iter.next(), Some("English"));
            assert!(iter.next().is_none());
            Result::Ok(())
        };
        closure().expect("Test failed");
    }

    #[test]
    fn subtree_tokens_postord() {
        let closure = move || {
            let root_data = 1usize;
            let (mut arena, root_token) = Arena::with_data(root_data)?;

            let first_child = root_token.append(&mut arena, 2usize)?;
            let second_child = root_token.append(&mut arena, 3usize)?;
            let third_child = root_token.append(&mut arena, 4usize)?;
            let first_grandchild = first_child.append(&mut arena, 0usize)?;
            let fourth_child = root_token.append(&mut arena, 5usize)?;
            let second_grandchild = second_child.append(&mut arena, 10usize)?;
            let third_grandchild = second_child.append(&mut arena, 20usize)?;
            let great_grandchild = third_grandchild.append(&mut arena, 20usize)?;

            let mut subtree = root_token.subtree_tokens(&arena, TraversalOrder::Post);
            assert_eq!(subtree.next(), Some(first_grandchild));
            assert_eq!(subtree.next(), Some(first_child));
            assert_eq!(subtree.next(), Some(second_grandchild));
            assert_eq!(subtree.next(), Some(great_grandchild));
            assert_eq!(subtree.next(), Some(third_grandchild));
            assert_eq!(subtree.next(), Some(second_child));
            assert_eq!(subtree.next(), Some(third_child));
            assert_eq!(subtree.next(), Some(fourth_child));
            assert_eq!(subtree.next(), Some(root_token));
            assert!(subtree.next().is_none());

            let mut subtree = great_grandchild.subtree_tokens(&arena, TraversalOrder::Post);
            assert_eq!(subtree.next(), Some(great_grandchild));
            assert!(subtree.next().is_none());
            Result::Ok(())
        };
        closure().expect("Test failed");
    }

    #[test]
    fn subtree_tokens_levelord() {
        let closure = move || {
            let root_data = 1usize;
            let (mut arena, root_token) = Arena::with_data(root_data)?;

            let first_child = root_token.append(&mut arena, 2usize)?;
            let second_child = root_token.append(&mut arena, 3usize)?;
            let third_child = root_token.append(&mut arena, 4usize)?;
            let first_grandchild = second_child.append(&mut arena, 10usize)?;
            let second_grandchild = second_child.append(&mut arena, 20usize)?;
            let fourth_child = root_token.append(&mut arena, 5usize)?;

            let mut subtree = root_token.subtree_tokens(&arena, TraversalOrder::Level);
            assert_eq!(subtree.next(), Some(root_token));
            assert_eq!(subtree.next(), Some(first_child));
            assert_eq!(subtree.next(), Some(second_child));
            assert_eq!(subtree.next(), Some(third_child));
            assert_eq!(subtree.next(), Some(fourth_child));
            assert_eq!(subtree.next(), Some(first_grandchild));
            assert_eq!(subtree.next(), Some(second_grandchild));
            assert!(subtree.next().is_none());

            let mut subtree = second_grandchild.subtree_tokens(&arena, TraversalOrder::Level);
            assert_eq!(subtree.next(), Some(second_grandchild));
            assert!(subtree.next().is_none());
            Result::Ok(())
        };
        closure().expect("Test failed");
    }

    #[test]
    fn subtree_postord() {
        let closure = move || {
            let root_data = "Indo-European";
            let (mut arena, root_token) = Arena::with_data(root_data)?;

            root_token.append(&mut arena, "Romance")?;
            root_token.append(&mut arena, "Germanic")?;
            let third_child = root_token.append(&mut arena, "Celtic")?;
            root_token.append(&mut arena, "Slavic")?;
            third_child.append(&mut arena, "Ulster")?;
            third_child.append(&mut arena, "Gaulish")?;

            let mut subtree = root_token.subtree(&arena, TraversalOrder::Post);
            assert_eq!(subtree.next().map(|c| c.data), Some("Romance"));
            assert_eq!(subtree.next().map(|c| c.data), Some("Germanic"));
            assert_eq!(subtree.next().map(|c| c.data), Some("Ulster"));
            assert_eq!(subtree.next().map(|c| c.data), Some("Gaulish"));
            assert_eq!(subtree.next().map(|c| c.data), Some("Celtic"));
            assert_eq!(subtree.next().map(|c| c.data), Some("Slavic"));
            assert_eq!(subtree.next().map(|c| c.data), Some("Indo-European"));
            assert!(subtree.next().is_none());
            Result::Ok(())
        };
        closure().expect("Test failed");
    }

    #[test]
    fn subtree_levelord() {
        let closure = move || {
            let root_data = "Indo-European";
            let (mut arena, root_token) = Arena::with_data(root_data)?;

            root_token.append(&mut arena, "Romance")?;
            root_token.append(&mut arena, "Germanic")?;
            let third_child = root_token.append(&mut arena, "Slavic")?;
            root_token.append(&mut arena, "Hellenic")?;
            third_child.append(&mut arena, "Russian")?;
            third_child.append(&mut arena, "Ukrainian")?;

            let mut subtree = root_token.subtree(&arena, TraversalOrder::Level);
            assert_eq!(subtree.next().map(|c| c.data), Some("Indo-European"));
            assert_eq!(subtree.next().map(|c| c.data), Some("Romance"));
            assert_eq!(subtree.next().map(|c| c.data), Some("Germanic"));
            assert_eq!(subtree.next().map(|c| c.data), Some("Slavic"));
            assert_eq!(subtree.next().map(|c| c.data), Some("Hellenic"));
            assert_eq!(subtree.next().map(|c| c.data), Some("Russian"));
            assert_eq!(subtree.next().map(|c| c.data), Some("Ukrainian"));
            assert!(subtree.next().is_none());
            Result::Ok(())
        };
        closure().expect("Test failed");
    }

    #[test]
    fn subtree_postord_mut() {
        let closure = move || {
            let root_data = 1usize;
            let (mut arena, root_token) = Arena::with_data(root_data)?;

            root_token.append(&mut arena, 2usize)?;
            root_token.append(&mut arena, 3usize)?;
            let third_child = root_token.append(&mut arena, 4usize)?;
            root_token.append(&mut arena, 5usize)?;
            third_child.append(&mut arena, 10usize)?;
            third_child.append(&mut arena, 20usize)?;

            for x in root_token.subtree_mut(&mut arena, TraversalOrder::Post) {
                x.data += 100;
            }

            let mut subtree = root_token.subtree(&arena, TraversalOrder::Post);
            assert_eq!(subtree.next().map(|c| c.data), Some(102));
            assert_eq!(subtree.next().map(|c| c.data), Some(103));
            assert_eq!(subtree.next().map(|c| c.data), Some(110));
            assert_eq!(subtree.next().map(|c| c.data), Some(120));
            assert_eq!(subtree.next().map(|c| c.data), Some(104));
            assert_eq!(subtree.next().map(|c| c.data), Some(105));
            assert_eq!(subtree.next().map(|c| c.data), Some(101));
            assert!(subtree.next().is_none());
            Result::Ok(())
        };
        closure().expect("Test failed");
    }

    #[test]
    fn subtree_levelord_mut() {
        let closure = move || {
            let root_data = 1usize;
            let (mut arena, root_token) = Arena::with_data(root_data)?;

            root_token.append(&mut arena, 2usize)?;
            root_token.append(&mut arena, 3usize)?;
            let third_child = root_token.append(&mut arena, 4usize)?;
            root_token.append(&mut arena, 5usize)?;
            third_child.append(&mut arena, 10usize)?;
            third_child.append(&mut arena, 20usize)?;

            for x in root_token.subtree_mut(&mut arena, TraversalOrder::Level) {
                x.data += 100;
            }

            let mut subtree = root_token.subtree(&arena, TraversalOrder::Level);
            assert_eq!(subtree.next().map(|c| c.data), Some(101));
            assert_eq!(subtree.next().map(|c| c.data), Some(102));
            assert_eq!(subtree.next().map(|c| c.data), Some(103));
            assert_eq!(subtree.next().map(|c| c.data), Some(104));
            assert_eq!(subtree.next().map(|c| c.data), Some(105));
            assert_eq!(subtree.next().map(|c| c.data), Some(110));
            assert_eq!(subtree.next().map(|c| c.data), Some(120));
            assert!(subtree.next().is_none());
            Result::Ok(())
        };
        closure().expect("Test failed");
    }

    #[test]
    fn remove_descendants() {
        let closure = move || {
            let root_data = 1usize;
            let (mut arena, root_token) = Arena::with_data(root_data)?;

            let first_child = root_token.append(&mut arena, 2usize)?;
            let second_child = root_token.append(&mut arena, 3usize)?;
            let third_child = root_token.append(&mut arena, 4usize)?;
            let fourth_child = root_token.append(&mut arena, 5usize)?;
            let grandchild_1 = third_child.append(&mut arena, 10usize)?;
            third_child.append(&mut arena, 20usize)?;
            grandchild_1.append(&mut arena, 100usize)?;

            assert_eq!(arena.node_count(), 8);

            third_child.remove_descendants(&mut arena);

            let mut subtree = root_token.subtree_tokens(&arena, TraversalOrder::Pre);
            assert_eq!(subtree.next(), Some(root_token));
            assert_eq!(subtree.next(), Some(first_child));
            assert_eq!(subtree.next(), Some(second_child));
            assert_eq!(subtree.next(), Some(third_child));
            assert_eq!(subtree.next(), Some(fourth_child));
            assert!(subtree.next().is_none());

            assert_eq!(arena.node_count(), 5);
            Result::Ok(())
        };
        closure().expect("Test failed");
    }
}
