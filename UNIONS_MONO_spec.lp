require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3348272 [_87154] (s : El (fun (fun _87154 bool) bool)) (t : El (fun (fun _87154 bool) bool)) : Prf (⇒ (∀ (λ x : El (fun _87154 bool), (⇒ ((@IN (fun _87154 bool)) x s) (∃ (λ y : El (fun _87154 bool), (∧ ((@IN (fun _87154 bool)) y t) ((@SUBSET _87154) x y))))))) ((@SUBSET _87154) ((@UNIONS _87154) s) ((@UNIONS _87154) t)));
