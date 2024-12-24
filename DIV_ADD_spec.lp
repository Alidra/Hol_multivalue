require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3111295 : Prf (∀ (λ d : El num, (∀ (λ a : El num, (∀ (λ b : El num, (⇒ (∨ (num_divides d a) (num_divides d b)) (= (DIV (+ a b) d) (+ (DIV a d) (DIV b d))))))))));
