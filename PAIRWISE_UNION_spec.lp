require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem4821878 [_110859] : Prf (∀ (λ R : El (fun _110859 (fun _110859 bool)), (∀ (λ s : El (fun _110859 bool), (∀ (λ t : El (fun _110859 bool), (= ((@pairwise _110859) R ((@UNION _110859) s t)) (∧ ((@pairwise _110859) R s) (∧ ((@pairwise _110859) R t) (∀ (λ x : El _110859, (∀ (λ y : El _110859, (⇒ (∧ ((@IN _110859) x ((@DIFF _110859) s t)) ((@IN _110859) y ((@DIFF _110859) t s))) (∧ (R x y) (R y x))))))))))))))));
