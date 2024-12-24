require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3326952 [_86883] : Prf (∀ (λ P : El (fun _86883 bool), (∀ (λ s : El (fun (fun _86883 bool) bool), (= (∀ (λ x : El _86883, (⇒ ((@IN _86883) x ((@UNIONS _86883) s)) (P x)))) (∀ (λ t : El (fun _86883 bool), (∀ (λ x : El _86883, (⇒ (∧ ((@IN (fun _86883 bool)) t s) ((@IN _86883) x t)) (P x)))))))))));
