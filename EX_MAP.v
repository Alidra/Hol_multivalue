Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import EX_MAP_term_abbrevs.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import o_THM_spec.
Require Import thm0_spec.
Require Import thm1094346_spec.
Require Import thm1094347_spec.
Require Import thm1097797_spec.
Require Import thm1101587_spec.
Require Import thm1101588_spec.
Require Import thm1101596_spec.
Require Import thm1101597_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem1139085 {A : Type'} (P : type1143 A) : term0 A P.
Proof. exact (EQ_MP (@lem1094347 A P) (@lem1094346 A P)). Qed.
Lemma lem1139086 {_26848 : Type'} (P : type1143 _26848) : term0 _26848 P.
Proof. exact (@lem1139085 _26848 P). Qed.
Lemma lem1139087 {_26848 _26849 : Type'} (P : _26849 -> Prop) (f : _26848 -> _26849) : term1 _26848 _26849 P f.
Proof. exact (@lem1139086 _26848 (term2 _26848 _26849 P f)). Qed.
Lemma lem1139088 {_26848 _26849 : Type'} (P : _26849 -> Prop) (f : _26848 -> _26849) : (term3 _26848 _26849 P f) = ((term4 _26848 _26849 P f) = (term5 _26848 _26849 P f)).
Proof. exact (eq_refl (term3 _26848 _26849 P f)). Qed.
Lemma lem1139089 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1139090 {_26848 _26849 : Type'} (P : _26849 -> Prop) (f : _26848 -> _26849) : (term6 _26848 _26849 P f) = (term7 _26848 _26849 P f).
Proof. exact (MK_COMB (@lem1139089) (@lem1139088 _26848 _26849 P f)). Qed.
Lemma lem1139091 {_26848 _26849 : Type'} (P : _26849 -> Prop) (f : _26848 -> _26849) (t : list _26848) : (term8 _26848 _26849 P f t) = ((term9 _26848 _26849 P f t) = (term10 _26848 _26849 P f t)).
Proof. exact (eq_refl (term8 _26848 _26849 P f t)). Qed.
Lemma lem1139092 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1139093 {_26848 _26849 : Type'} (P : _26849 -> Prop) (f : _26848 -> _26849) (t : list _26848) : (term11 _26848 _26849 P f t) = (term12 _26848 _26849 P f t).
Proof. exact (MK_COMB (@lem1139092) (@lem1139091 _26848 _26849 P f t)). Qed.
Lemma lem1139094 {_26848 _26849 : Type'} (P : _26849 -> Prop) (f : _26848 -> _26849) (h : _26848) (t : list _26848) : (term13 _26848 _26849 P f h t) = ((term14 _26848 _26849 P f h t) = (term15 _26848 _26849 P f h t)).
Proof. exact (eq_refl (term13 _26848 _26849 P f h t)). Qed.
Lemma lem1139095 {_26848 _26849 : Type'} (P : _26849 -> Prop) (f : _26848 -> _26849) (h : _26848) (t : list _26848) : (term16 _26848 _26849 P f h t) = (term17 _26848 _26849 P f h t).
Proof. exact (MK_COMB (@lem1139093 _26848 _26849 P f t) (@lem1139094 _26848 _26849 P f h t)). Qed.
Lemma lem1139096 {_26848 _26849 : Type'} (P : _26849 -> Prop) (f : _26848 -> _26849) (h : _26848) : (term18 _26848 _26849 P f h) = (term19 _26848 _26849 P f h).
Proof. exact (fun_ext (fun t : list _26848 => @lem1139095 _26848 _26849 P f h t)). Qed.
Lemma lem1139097 {_26848 : Type'} : (@all (list _26848)) = (@all (list _26848)).
Proof. exact (eq_refl (@all (list _26848))). Qed.
Lemma lem1139098 {_26848 _26849 : Type'} (P : _26849 -> Prop) (f : _26848 -> _26849) (h : _26848) : (term20 _26848 _26849 P f h) = (term21 _26848 _26849 P f h).
Proof. exact (MK_COMB (@lem1139097 _26848) (@lem1139096 _26848 _26849 P f h)). Qed.
Lemma lem1139099 {_26848 _26849 : Type'} (P : _26849 -> Prop) (f : _26848 -> _26849) : (term22 _26848 _26849 P f) = (term23 _26848 _26849 P f).
Proof. exact (fun_ext (fun h : _26848 => @lem1139098 _26848 _26849 P f h)). Qed.
Lemma lem1139100 {_26848 : Type'} : (@all _26848) = (@all _26848).
Proof. exact (eq_refl (@all _26848)). Qed.
Lemma lem1139101 {_26848 _26849 : Type'} (P : _26849 -> Prop) (f : _26848 -> _26849) : (term24 _26848 _26849 P f) = (term25 _26848 _26849 P f).
Proof. exact (MK_COMB (@lem1139100 _26848) (@lem1139099 _26848 _26849 P f)). Qed.
Lemma lem1139102 {_26848 _26849 : Type'} (P : _26849 -> Prop) (f : _26848 -> _26849) : (term26 _26848 _26849 P f) = (term27 _26848 _26849 P f).
Proof. exact (MK_COMB (@lem1139090 _26848 _26849 P f) (@lem1139101 _26848 _26849 P f)). Qed.
Lemma lem1139103 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1139104 {_26848 _26849 : Type'} (P : _26849 -> Prop) (f : _26848 -> _26849) : (term28 _26848 _26849 P f) = (term29 _26848 _26849 P f).
Proof. exact (MK_COMB (@lem1139103) (@lem1139102 _26848 _26849 P f)). Qed.
Lemma lem1139105 {_26848 _26849 : Type'} (P : _26849 -> Prop) (f : _26848 -> _26849) (l : list _26848) : (term8 _26848 _26849 P f l) = ((term9 _26848 _26849 P f l) = (term10 _26848 _26849 P f l)).
Proof. exact (eq_refl (term8 _26848 _26849 P f l)). Qed.
Lemma lem1139106 {_26848 _26849 : Type'} (P : _26849 -> Prop) (f : _26848 -> _26849) : (term30 _26848 _26849 P f) = (term2 _26848 _26849 P f).
Proof. exact (fun_ext (fun l : list _26848 => @lem1139105 _26848 _26849 P f l)). Qed.
Lemma lem1139107 {_26848 : Type'} : (@all (list _26848)) = (@all (list _26848)).
Proof. exact (eq_refl (@all (list _26848))). Qed.
Lemma lem1139108 {_26848 _26849 : Type'} (P : _26849 -> Prop) (f : _26848 -> _26849) : (term31 _26848 _26849 P f) = (term32 _26848 _26849 P f).
Proof. exact (MK_COMB (@lem1139107 _26848) (@lem1139106 _26848 _26849 P f)). Qed.
Lemma lem1139109 {_26848 _26849 : Type'} (P : _26849 -> Prop) (f : _26848 -> _26849) : (term1 _26848 _26849 P f) = (term33 _26848 _26849 P f).
Proof. exact (MK_COMB (@lem1139104 _26848 _26849 P f) (@lem1139108 _26848 _26849 P f)). Qed.
Lemma lem1139110 {_26848 _26849 : Type'} (P : _26849 -> Prop) (f : _26848 -> _26849) : term33 _26848 _26849 P f.
Proof. exact (EQ_MP (@lem1139109 _26848 _26849 P f) (@lem1139087 _26848 _26849 P f)). Qed.
Lemma lem1139133 {A B : Type'} : term34 A B.
Proof. exact (proj1 (@lem1097797 A B)). Qed.
Lemma lem1139134 {A B : Type'} (f : A -> B) : term35 A B f.
Proof. exact (@lem1139133 A B f). Qed.
Lemma lem1139135 {A B : Type'} (f : A -> B) : (term35 A B f) = ((@List.map A B f (@nil A)) = (@nil B)).
Proof. exact (eq_refl (term35 A B f)). Qed.
Lemma lem1139140 {A B : Type'} (f : A -> B) : (@List.map A B f (@nil A)) = (@nil B).
Proof. exact (EQ_MP (@lem1139135 A B f) (@lem1139134 A B f)). Qed.
Lemma lem1139141 {_26848 _26849 : Type'} (f : _26848 -> _26849) : (@List.map _26848 _26849 f (@nil _26848)) = (@nil _26849).
Proof. exact (@lem1139140 _26848 _26849 f). Qed.
Lemma lem1139142 {_26849 : Type'} (P : _26849 -> Prop) : (@EX _26849 P) = (@EX _26849 P).
Proof. exact (eq_refl (@EX _26849 P)). Qed.
Lemma lem1139143 {_26848 _26849 : Type'} (f : _26848 -> _26849) (P : _26849 -> Prop) : (term4 _26848 _26849 P f) = (@EX _26849 P (@nil _26849)).
Proof. exact (MK_COMB (@lem1139142 _26849 P) (@lem1139141 _26848 _26849 f)). Qed.
Lemma lem1139145 {_25328 : Type'} (P : _25328 -> Prop) : (@EX _25328 P (@nil _25328)) = False.
Proof. exact (EQ_MP (@lem1101588 _25328 P) (@lem1101587 _25328 P)). Qed.
Lemma lem1139146 {_26849 : Type'} (P : _26849 -> Prop) : (@EX _26849 P (@nil _26849)) = False.
Proof. exact (@lem1139145 _26849 P). Qed.
Lemma lem1139147 {_26848 _26849 : Type'} (P : _26849 -> Prop) (f : _26848 -> _26849) : (term4 _26848 _26849 P f) = False.
Proof. exact (TRANS (@lem1139143 _26848 _26849 f P) (@lem1139146 _26849 P)). Qed.
Lemma lem1139148 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1139149 {_26848 _26849 : Type'} (P : _26849 -> Prop) (f : _26848 -> _26849) : (term36 _26848 _26849 P f) = (@eq Prop False).
Proof. exact (MK_COMB (@lem1139148) (@lem1139147 _26848 _26849 P f)). Qed.
Lemma lem1139151 {_25328 : Type'} (P : _25328 -> Prop) : (@EX _25328 P (@nil _25328)) = False.
Proof. exact (EQ_MP (@lem1101588 _25328 P) (@lem1101587 _25328 P)). Qed.
Lemma lem1139152 {_26848 : Type'} (P : _26848 -> Prop) : (@EX _26848 P (@nil _26848)) = False.
Proof. exact (@lem1139151 _26848 P). Qed.
Lemma lem1139153 {_26848 _26849 : Type'} (P : _26849 -> Prop) (f : _26848 -> _26849) : (term5 _26848 _26849 P f) = False.
Proof. exact (@lem1139152 _26848 (@o _26848 _26849 Prop P f)). Qed.
Lemma lem1139154 {_26848 _26849 : Type'} (P : _26849 -> Prop) (f : _26848 -> _26849) : ((term4 _26848 _26849 P f) = (term5 _26848 _26849 P f)) = (False = False).
Proof. exact (MK_COMB (@lem1139149 _26848 _26849 P f) (@lem1139153 _26848 _26849 P f)). Qed.
Lemma lem1139156 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem1139157 : (False = False) = (~ False).
Proof. exact (@lem1139156 False). Qed.
Lemma lem1139159 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1139160 : (False = False) = True.
Proof. exact (TRANS (@lem1139157) (@lem1139159)). Qed.
Lemma lem1139161 {_26848 _26849 : Type'} (P : _26849 -> Prop) (f : _26848 -> _26849) : ((term4 _26848 _26849 P f) = (term5 _26848 _26849 P f)) = True.
Proof. exact (TRANS (@lem1139154 _26848 _26849 P f) (@lem1139160)). Qed.
Lemma lem1139162 {_26848 _26849 : Type'} (P : _26849 -> Prop) (f : _26848 -> _26849) : True = ((term4 _26848 _26849 P f) = (term5 _26848 _26849 P f)).
Proof. exact (SYM (@lem1139161 _26848 _26849 P f)). Qed.
Lemma lem1139163 {_26848 _26849 : Type'} (P : _26849 -> Prop) (f : _26848 -> _26849) : (term4 _26848 _26849 P f) = (term5 _26848 _26849 P f).
Proof. exact (EQ_MP (@lem1139162 _26848 _26849 P f) (@lem0)). Qed.
Lemma lem1139164 {A B C : Type'} (f : B -> C) : term37 A B C f.
Proof. exact (@lem15456 A B C f). Qed.
Lemma lem1139165 {A B C : Type'} (f : B -> C) : (term37 A B C f) = (term38 A B C f).
Proof. exact (eq_refl (term37 A B C f)). Qed.
Lemma lem1139166 {A B C : Type'} (f : B -> C) : term38 A B C f.
Proof. exact (EQ_MP (@lem1139165 A B C f) (@lem1139164 A B C f)). Qed.
Lemma lem1139167 {A B C : Type'} (f : B -> C) (g : A -> B) : term39 A B C f g.
Proof. exact (@lem1139166 A B C f g). Qed.
Lemma lem1139168 {A B C : Type'} (f : B -> C) (g : A -> B) : (term39 A B C f g) = (term40 A B C f g).
Proof. exact (eq_refl (term39 A B C f g)). Qed.
Lemma lem1139169 {A B C : Type'} (f : B -> C) (g : A -> B) : term40 A B C f g.
Proof. exact (EQ_MP (@lem1139168 A B C f g) (@lem1139167 A B C f g)). Qed.
Lemma lem1139170 {A B C : Type'} (f : B -> C) (g : A -> B) (x : A) : term41 A B C f g x.
Proof. exact (@lem1139169 A B C f g x). Qed.
Lemma lem1139171 {A B C : Type'} (f : B -> C) (g : A -> B) (x : A) : (term41 A B C f g x) = ((@o A B C f g x) = (term42 A B C f g x)).
Proof. exact (eq_refl (term41 A B C f g x)). Qed.
Lemma lem1139175 {A B : Type'} : term43 A B.
Proof. exact (proj2 (@lem1097797 A B)). Qed.
Lemma lem1139176 {A B : Type'} (f : A -> B) : term44 A B f.
Proof. exact (@lem1139175 A B f). Qed.
Lemma lem1139177 {A B : Type'} (f : A -> B) : (term44 A B f) = (term45 A B f).
Proof. exact (eq_refl (term44 A B f)). Qed.
Lemma lem1139178 {A B : Type'} (f : A -> B) : term45 A B f.
Proof. exact (EQ_MP (@lem1139177 A B f) (@lem1139176 A B f)). Qed.
Lemma lem1139179 {A B : Type'} (f : A -> B) (h : A) : term46 A B f h.
Proof. exact (@lem1139178 A B f h). Qed.
Lemma lem1139180 {A B : Type'} (h : A) (f : A -> B) : (term46 A B f h) = (term47 A B h f).
Proof. exact (eq_refl (term46 A B f h)). Qed.
Lemma lem1139181 {A B : Type'} (h : A) (f : A -> B) : term47 A B h f.
Proof. exact (EQ_MP (@lem1139180 A B h f) (@lem1139179 A B f h)). Qed.
Lemma lem1139182 {A B : Type'} (h : A) (f : A -> B) (t : list A) : term48 A B h f t.
Proof. exact (@lem1139181 A B h f t). Qed.
Lemma lem1139183 {A B : Type'} (h : A) (f : A -> B) (t : list A) : (term48 A B h f t) = ((term49 A B f h t) = (term50 A B h f t)).
Proof. exact (eq_refl (term48 A B h f t)). Qed.
Lemma lem1139192 {A B : Type'} (h : A) (f : A -> B) (t : list A) : (term49 A B f h t) = (term50 A B h f t).
Proof. exact (EQ_MP (@lem1139183 A B h f t) (@lem1139182 A B h f t)). Qed.
Lemma lem1139193 {_26848 _26849 : Type'} (h : _26848) (f : _26848 -> _26849) (t : list _26848) : (term49 _26848 _26849 f h t) = (term50 _26848 _26849 h f t).
Proof. exact (@lem1139192 _26848 _26849 h f t). Qed.
Lemma lem1139194 {_26849 : Type'} (P : _26849 -> Prop) : (@EX _26849 P) = (@EX _26849 P).
Proof. exact (eq_refl (@EX _26849 P)). Qed.
Lemma lem1139195 {_26848 _26849 : Type'} (P : _26849 -> Prop) (h : _26848) (f : _26848 -> _26849) (t : list _26848) : (term14 _26848 _26849 P f h t) = (term51 _26848 _26849 P h f t).
Proof. exact (MK_COMB (@lem1139194 _26849 P) (@lem1139193 _26848 _26849 h f t)). Qed.
Lemma lem1139197 {_25328 : Type'} (h : _25328) (P : _25328 -> Prop) (t : list _25328) : (term52 _25328 P h t) = (term53 _25328 h P t).
Proof. exact (EQ_MP (@lem1101597 _25328 h P t) (@lem1101596 _25328 h P t)). Qed.
Lemma lem1139198 {_26849 : Type'} (h : _26849) (P : _26849 -> Prop) (t : list _26849) : (term52 _26849 P h t) = (term53 _26849 h P t).
Proof. exact (@lem1139197 _26849 h P t). Qed.
Lemma lem1139199 {_26848 _26849 : Type'} (h : _26848) (P : _26849 -> Prop) (f : _26848 -> _26849) (t : list _26848) : (term51 _26848 _26849 P h f t) = (term54 _26848 _26849 h P f t).
Proof. exact (@lem1139198 _26849 (f h) P (@List.map _26848 _26849 f t)). Qed.
Lemma lem1139203 {_26848 _26849 : Type'} (P : _26849 -> Prop) (f : _26848 -> _26849) (t : list _26848) (h1 : (term9 _26848 _26849 P f t) = (term10 _26848 _26849 P f t)) : (term9 _26848 _26849 P f t) = (term10 _26848 _26849 P f t).
Proof. exact (h1). Qed.
Lemma lem1139204 {_26848 _26849 : Type'} (P : _26849 -> Prop) (f : _26848 -> _26849) (h : _26848) : (term55 _26848 _26849 P f h) = (term55 _26848 _26849 P f h).
Proof. exact (eq_refl (term55 _26848 _26849 P f h)). Qed.
Lemma lem1139205 {_26848 _26849 : Type'} (h : _26848) (P : _26849 -> Prop) (f : _26848 -> _26849) (t : list _26848) (h1 : (term9 _26848 _26849 P f t) = (term10 _26848 _26849 P f t)) : (term54 _26848 _26849 h P f t) = (term56 _26848 _26849 h P f t).
Proof. exact (MK_COMB (@lem1139204 _26848 _26849 P f h) (@lem1139203 _26848 _26849 P f t h1)). Qed.
Lemma lem1139208 {_26848 _26849 : Type'} (h : _26848) (P : _26849 -> Prop) (f : _26848 -> _26849) (t : list _26848) (h1 : (term9 _26848 _26849 P f t) = (term10 _26848 _26849 P f t)) : (term51 _26848 _26849 P h f t) = (term56 _26848 _26849 h P f t).
Proof. exact (TRANS (@lem1139199 _26848 _26849 h P f t) (@lem1139205 _26848 _26849 h P f t h1)). Qed.
Lemma lem1139209 {_26848 _26849 : Type'} (h : _26848) (P : _26849 -> Prop) (f : _26848 -> _26849) (t : list _26848) (h1 : (term9 _26848 _26849 P f t) = (term10 _26848 _26849 P f t)) : (term14 _26848 _26849 P f h t) = (term56 _26848 _26849 h P f t).
Proof. exact (TRANS (@lem1139195 _26848 _26849 P h f t) (@lem1139208 _26848 _26849 h P f t h1)). Qed.
Lemma lem1139210 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1139211 {_26848 _26849 : Type'} (h : _26848) (P : _26849 -> Prop) (f : _26848 -> _26849) (t : list _26848) (h1 : (term9 _26848 _26849 P f t) = (term10 _26848 _26849 P f t)) : (term57 _26848 _26849 P f h t) = (term58 _26848 _26849 h P f t).
Proof. exact (MK_COMB (@lem1139210) (@lem1139209 _26848 _26849 h P f t h1)). Qed.
Lemma lem1139213 {_25328 : Type'} (h : _25328) (P : _25328 -> Prop) (t : list _25328) : (term52 _25328 P h t) = (term53 _25328 h P t).
Proof. exact (EQ_MP (@lem1101597 _25328 h P t) (@lem1101596 _25328 h P t)). Qed.
Lemma lem1139214 {_26848 : Type'} (h : _26848) (P : _26848 -> Prop) (t : list _26848) : (term52 _26848 P h t) = (term53 _26848 h P t).
Proof. exact (@lem1139213 _26848 h P t). Qed.
Lemma lem1139215 {_26848 _26849 : Type'} (h : _26848) (P : _26849 -> Prop) (f : _26848 -> _26849) (t : list _26848) : (term15 _26848 _26849 P f h t) = (term59 _26848 _26849 h P f t).
Proof. exact (@lem1139214 _26848 h (@o _26848 _26849 Prop P f) t). Qed.
Lemma lem1139219 {A B C : Type'} (f : B -> C) (g : A -> B) (x : A) : (@o A B C f g x) = (term42 A B C f g x).
Proof. exact (EQ_MP (@lem1139171 A B C f g x) (@lem1139170 A B C f g x)). Qed.
Lemma lem1139220 {_26848 _26849 : Type'} (f : _26849 -> Prop) (g : _26848 -> _26849) (x : _26848) : (@o _26848 _26849 Prop f g x) = (term60 _26848 _26849 f g x).
Proof. exact (@lem1139219 _26848 _26849 Prop f g x). Qed.
Lemma lem1139221 {_26848 _26849 : Type'} (P : _26849 -> Prop) (f : _26848 -> _26849) (h : _26848) : (@o _26848 _26849 Prop P f h) = (term60 _26848 _26849 P f h).
Proof. exact (@lem1139220 _26848 _26849 P f h). Qed.
Lemma lem1139222 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1139223 {_26848 _26849 : Type'} (P : _26849 -> Prop) (f : _26848 -> _26849) (h : _26848) : (term61 _26848 _26849 P f h) = (term55 _26848 _26849 P f h).
Proof. exact (MK_COMB (@lem1139222) (@lem1139221 _26848 _26849 P f h)). Qed.
Lemma lem1139224 {_26848 _26849 : Type'} (P : _26849 -> Prop) (f : _26848 -> _26849) (t : list _26848) : (term10 _26848 _26849 P f t) = (term10 _26848 _26849 P f t).
Proof. exact (eq_refl (term10 _26848 _26849 P f t)). Qed.
Lemma lem1139225 {_26848 _26849 : Type'} (h : _26848) (P : _26849 -> Prop) (f : _26848 -> _26849) (t : list _26848) : (term59 _26848 _26849 h P f t) = (term56 _26848 _26849 h P f t).
Proof. exact (MK_COMB (@lem1139223 _26848 _26849 P f h) (@lem1139224 _26848 _26849 P f t)). Qed.
Lemma lem1139228 {_26848 _26849 : Type'} (h : _26848) (P : _26849 -> Prop) (f : _26848 -> _26849) (t : list _26848) : (term15 _26848 _26849 P f h t) = (term56 _26848 _26849 h P f t).
Proof. exact (TRANS (@lem1139215 _26848 _26849 h P f t) (@lem1139225 _26848 _26849 h P f t)). Qed.
Lemma lem1139229 {_26848 _26849 : Type'} (h : _26848) (P : _26849 -> Prop) (f : _26848 -> _26849) (t : list _26848) (h1 : (term9 _26848 _26849 P f t) = (term10 _26848 _26849 P f t)) : ((term14 _26848 _26849 P f h t) = (term15 _26848 _26849 P f h t)) = ((term56 _26848 _26849 h P f t) = (term56 _26848 _26849 h P f t)).
Proof. exact (MK_COMB (@lem1139211 _26848 _26849 h P f t h1) (@lem1139228 _26848 _26849 h P f t)). Qed.
Lemma lem1139231 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1139232 (x : Prop) : (x = x) = True.
Proof. exact (@lem1139231 Prop x). Qed.
Lemma lem1139233 {_26848 _26849 : Type'} (h : _26848) (P : _26849 -> Prop) (f : _26848 -> _26849) (t : list _26848) : ((term56 _26848 _26849 h P f t) = (term56 _26848 _26849 h P f t)) = True.
Proof. exact (@lem1139232 (term56 _26848 _26849 h P f t)). Qed.
Lemma lem1139234 {_26848 _26849 : Type'} (h : _26848) (P : _26849 -> Prop) (f : _26848 -> _26849) (t : list _26848) (h1 : (term9 _26848 _26849 P f t) = (term10 _26848 _26849 P f t)) : ((term14 _26848 _26849 P f h t) = (term15 _26848 _26849 P f h t)) = True.
Proof. exact (TRANS (@lem1139229 _26848 _26849 h P f t h1) (@lem1139233 _26848 _26849 h P f t)). Qed.
Lemma lem1139235 {_26848 _26849 : Type'} (h : _26848) (P : _26849 -> Prop) (f : _26848 -> _26849) (t : list _26848) (h1 : (term9 _26848 _26849 P f t) = (term10 _26848 _26849 P f t)) : True = ((term14 _26848 _26849 P f h t) = (term15 _26848 _26849 P f h t)).
Proof. exact (SYM (@lem1139234 _26848 _26849 h P f t h1)). Qed.
Lemma lem1139236 {_26848 _26849 : Type'} (h : _26848) (P : _26849 -> Prop) (f : _26848 -> _26849) (t : list _26848) (h1 : (term9 _26848 _26849 P f t) = (term10 _26848 _26849 P f t)) : (term14 _26848 _26849 P f h t) = (term15 _26848 _26849 P f h t).
Proof. exact (EQ_MP (@lem1139235 _26848 _26849 h P f t h1) (@lem0)). Qed.
Lemma lem1139237 {_26848 _26849 : Type'} (P : _26849 -> Prop) (f : _26848 -> _26849) (h : _26848) (t : list _26848) : term17 _26848 _26849 P f h t.
Proof. exact (fun h0 : (term9 _26848 _26849 P f t) = (term10 _26848 _26849 P f t) => @lem1139236 _26848 _26849 h P f t h0). Qed.
Lemma lem1139242 {_26848 _26849 : Type'} (P : _26849 -> Prop) (f : _26848 -> _26849) (h : _26848) : term21 _26848 _26849 P f h.
Proof. exact (fun t : list _26848 => @lem1139237 _26848 _26849 P f h t). Qed.
Lemma lem1139247 {_26848 _26849 : Type'} (P : _26849 -> Prop) (f : _26848 -> _26849) : term25 _26848 _26849 P f.
Proof. exact (fun h : _26848 => @lem1139242 _26848 _26849 P f h). Qed.
Lemma lem1139248 {_26848 _26849 : Type'} (P : _26849 -> Prop) (f : _26848 -> _26849) : term27 _26848 _26849 P f.
Proof. exact (conj (@lem1139163 _26848 _26849 P f) (@lem1139247 _26848 _26849 P f)). Qed.
Lemma lem1139249 {_26848 _26849 : Type'} (P : _26849 -> Prop) (f : _26848 -> _26849) : term32 _26848 _26849 P f.
Proof. exact (@lem1139110 _26848 _26849 P f (@lem1139248 _26848 _26849 P f)). Qed.
Lemma lem1139254 {_26848 _26849 : Type'} (P : _26849 -> Prop) : term62 _26848 _26849 P.
Proof. exact (fun f : _26848 -> _26849 => @lem1139249 _26848 _26849 P f). Qed.
Lemma lem1139259 {_26848 _26849 : Type'} : term63 _26848 _26849.
Proof. exact (fun P : _26849 -> Prop => @lem1139254 _26848 _26849 P). Qed.
