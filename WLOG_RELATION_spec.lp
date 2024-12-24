require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7661 [_1718] : Prf (∀ (λ R : El (fun _1718 (fun _1718 bool)), (∀ (λ P : El (fun _1718 (fun _1718 bool)), (⇒ (∧ (∀ (λ x : El _1718, (∀ (λ y : El _1718, (⇒ (P x y) (P y x)))))) (∧ (∀ (λ x : El _1718, (∀ (λ y : El _1718, (∨ (R x y) (R y x)))))) (∀ (λ x : El _1718, (∀ (λ y : El _1718, (⇒ (R x y) (P x y)))))))) (∀ (λ x : El _1718, (∀ (λ y : El _1718, (P x y))))))))));
