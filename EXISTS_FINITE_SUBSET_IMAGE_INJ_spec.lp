require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3688903 [_93670 _93677] : Prf (∀ (λ P : El (fun (fun _93677 bool) bool), (∀ (λ f : El (fun _93670 _93677), (∀ (λ s : El (fun _93670 bool), (= (∃ (λ t : El (fun _93677 bool), (∧ ((@FINITE _93677) t) (∧ ((@SUBSET _93677) t ((@IMAGE _93670 _93677) f s)) (P t))))) (∃ (λ t : El (fun _93670 bool), (∧ ((@FINITE _93670) t) (∧ ((@SUBSET _93670) t s) (∧ (∀ (λ x : El _93670, (∀ (λ y : El _93670, (⇒ (∧ ((@IN _93670) x t) ((@IN _93670) y t)) (= (= (f x) (f y)) (= x y))))))) (P ((@IMAGE _93670 _93677) f t))))))))))))));
