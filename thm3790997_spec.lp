require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3790997 [A B] : Prf (∧ (∀ (λ f : El (fun A (fun B B)), (∀ (λ s : El (fun A bool), (∀ (λ a : El B, (∀ (λ b : El B, (= ((@FINREC A B) f b s a (NUMERAL _0)) (∧ (= s (@EMPTY A)) (= a b))))))))))) (∀ (λ b : El B, (∀ (λ s : El (fun A bool), (∀ (λ n : El num, (∀ (λ a : El B, (∀ (λ f : El (fun A (fun B B)), (= ((@FINREC A B) f b s a (SUC n)) (∃ (λ x : El A, (∃ (λ c : El B, (∧ ((@IN A) x s) (∧ ((@FINREC A B) f b ((@DELETE A) s x) c n) (= a (f x c))))))))))))))))))));
