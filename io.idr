module stdlib.io

import stdlib.monads

%access public

abstract data IO a =
    prim__IO a

abstract
io_bind : IO a -> (a -> IO b) -> IO b
io_bind (prim__IO v) k =
    k v

abstract
io_return : a -> IO a
io_return x =
    prim__IO x

run__IO : IO () -> IO ()
run__IO v =
    io_bind v (\v' => io_return v')

instance Monad IO where
    return x = io_return x
    b >>= k = io_bind b k

{-
putString : String -> IO ()
putString s =
    mkForeign (FFun "putStr" [FString] FUnit) x
-}
