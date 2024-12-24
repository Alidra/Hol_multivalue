require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1322260 : Prf (∀ (λ a : El hreal, (∀ (λ b : El hreal, (∀ (λ c : El hreal, (⇒ (hreal_le a b) (hreal_le (hreal_mul a c) (hreal_mul b c)))))))));
