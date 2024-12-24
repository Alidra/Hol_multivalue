require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem367111 [_16436] (a : El _16436) (m : El (fun _16436 num)) (b : El _16436) : Prf (= (∀ (λ y : El _16436, (⇒ ((@MEASURE _16436) m y a) ((@MEASURE _16436) m y b)))) (<= (m a) (m b)));
