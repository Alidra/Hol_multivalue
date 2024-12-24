require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem5715484 [_119721] : Prf (∀ (λ op : El (fun _119721 (fun _119721 _119721)), (⇒ ((@monoidal _119721) op) (∧ (∀ (λ a : El _119721, (= (op ((@neutral _119721) op) a) a))) (∧ (∀ (λ a : El _119721, (= (op a ((@neutral _119721) op)) a))) (∧ (∀ (λ a : El _119721, (∀ (λ b : El _119721, (= (op a b) (op b a)))))) (∧ (∀ (λ a : El _119721, (∀ (λ b : El _119721, (∀ (λ c : El _119721, (= (op (op a b) c) (op a (op b c))))))))) (∀ (λ a : El _119721, (∀ (λ b : El _119721, (∀ (λ c : El _119721, (= (op a (op b c)) (op b (op a c))))))))))))))));
