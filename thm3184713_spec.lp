require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3184713 [_83152] (p : El (fun _83152 bool)) : Prf (∀ (λ x : El _83152, (= ((@GSPEC _83152) (λ v : El _83152, (∃ (λ y : El _83152, ((@SETSPEC _83152) v (p y) y)))) x) (p x))));
