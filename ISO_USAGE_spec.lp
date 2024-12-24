require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1079952 [_24632 _24635] (g : El (fun _24632 _24635)) (f : El (fun _24635 _24632)) : Prf (⇒ ((@ISO _24635 _24632) f g) (∧ (∀ (λ P : El (fun _24635 bool), (= (∀ (λ x : El _24635, (P x))) (∀ (λ x : El _24632, (P (g x))))))) (∧ (∀ (λ P : El (fun _24635 bool), (= (∃ (λ x : El _24635, (P x))) (∃ (λ x : El _24632, (P (g x))))))) (∀ (λ a : El _24635, (∀ (λ b : El _24632, (= (= a (g b)) (= (f a) b)))))))));
