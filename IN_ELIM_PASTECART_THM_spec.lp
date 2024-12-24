require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem8002422 [_141774 _141775 _141776] : Prf (∀ (λ P : El (fun (cart _141774 _141775) (fun (cart _141774 _141776) bool)), (∀ (λ a : El (cart _141774 _141775), (∀ (λ b : El (cart _141774 _141776), (= ((@IN (cart _141774 (finite_sum _141775 _141776))) ((@pastecart _141774 _141775 _141776) a b) ((@GSPEC (cart _141774 (finite_sum _141775 _141776))) (λ GEN_PVAR_360 : El (cart _141774 (finite_sum _141775 _141776)), (∃ (λ x : El (cart _141774 _141775), (∃ (λ y : El (cart _141774 _141776), ((@SETSPEC (cart _141774 (finite_sum _141775 _141776))) GEN_PVAR_360 (P x y) ((@pastecart _141774 _141775 _141776) x y))))))))) (P a b))))))));
