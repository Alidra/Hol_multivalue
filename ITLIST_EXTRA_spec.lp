require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1129577 [_26663 _26664] (f : El (fun _26664 (fun _26663 _26663))) (a : El _26664) (b : El _26663) : Prf (∀ (λ l : El (list _26664), (= ((@ITLIST _26663 _26664) f ((@APPEND _26664) l ((@CONS _26664) a (@NIL _26664))) b) ((@ITLIST _26663 _26664) f l (f a b)))));
