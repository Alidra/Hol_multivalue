require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3791024 [A B] (b : El B) (s : El (fun A bool)) (n : El num) (a : El B) (f : El (fun A (fun B B))) : Prf ((λ f' : El (fun A (fun B B)), (= ((@FINREC A B) f' b s a (SUC n)) (∃ (λ x : El A, (∃ (λ c : El B, (∧ ((@IN A) x s) (∧ ((@FINREC A B) f' b ((@DELETE A) s x) c n) (= a (f' x c)))))))))) f);
