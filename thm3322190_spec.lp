require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3322190 [_86807] (s : El (fun _86807 bool)) : Prf (= (∀ (λ x : El _86807, (= ((@IN _86807) x ((@UNIONS _86807) ((@INSERT (fun _86807 bool)) s (@EMPTY (fun _86807 bool))))) ((@IN _86807) x s)))) (= ((@UNIONS _86807) ((@INSERT (fun _86807 bool)) s (@EMPTY (fun _86807 bool)))) s));
