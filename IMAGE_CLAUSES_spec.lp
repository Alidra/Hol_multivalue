require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3366870 [_87477 _87481] (x : El _87477) (f : El (fun _87477 _87481)) (s : El (fun _87477 bool)) : Prf (∧ (= ((@IMAGE _87477 _87481) f (@EMPTY _87477)) (@EMPTY _87481)) (= ((@IMAGE _87477 _87481) f ((@INSERT _87477) x s)) ((@INSERT _87481) (f x) ((@IMAGE _87477 _87481) f s))));
