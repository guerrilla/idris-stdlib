module stdlib.monads

%access public

infixl 5 >>=

class Monad (m : Set -> Set) where
    return : a -> m a
    (>>=) : m a -> (a -> m b) -> m b
