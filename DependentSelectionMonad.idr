module Main

import Data.HVect

record J r x where
    constructor j
    unJ : (x -> r) -> x

bind : J r x -> (x -> J r y) -> J r y
bind m k = j (\ p : (y -> r) => unJ (k (unJ m (p . flip (unJ . k) p))) p)

return : x -> J r x
return a = j (\_ => a)

ap : (J r (x -> y)) -> J r x -> J r y
ap f a = bind f (\xf => bind a (\xa => return (xf xa)))

fmap : (a -> b) -> J r a -> J r b
fmap f fa = ap (return f) fa

implementation Functor (J r) where
    map = fmap

implementation Applicative (J r) where
    pure  = return
    (<*>) = ap

implementation Monad (J r) where
    (>>=) = bind

-------------------------------------------------------------------------

jify : Type -> (Vect a Type) -> (Vect a Type)
jify r = map (J r)

jsequence : {auto a : Vect x Type} -> HVect (jify r a) -> J r (HVect a)
jsequence {a = []} []         = return []
jsequence {a = t::ts} (xm::xms) = do x  <- xm
                                     xs <- jsequence xms
                                     return (x::xs)

jsequence' : {auto a : Vect x Type} -> HVect (jify r a) -> J r (HVect a)
jsequence' {a = []} []           = j $ \p => []
jsequence' {a = t::ts} (xm::xms) = j $ \p => let z = unJ xm (\y => p (y :: (unJ (jsequence' xms) (\a => p (y :: a))))) in
                                                 z :: unJ (jsequence' xms) (\x => p (z :: x))
        
