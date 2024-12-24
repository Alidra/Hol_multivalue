Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import IN_INTER_term_abbrevs.
Require Import INTER_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm3184736_spec.
Require Import thm3184739_spec.
Lemma lem3205092 {A : Type'} (s : A -> Prop) : term0 A s.
Proof. exact (@lem3190197 A s). Qed.
Lemma lem3205093 {A : Type'} (s : A -> Prop) : (term0 A s) = (term1 A s).
Proof. exact (eq_refl (term0 A s)). Qed.
Lemma lem3205094 {A : Type'} (s : A -> Prop) : term1 A s.
Proof. exact (EQ_MP (@lem3205093 A s) (@lem3205092 A s)). Qed.
Lemma lem3205095 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term2 A s t.
Proof. exact (@lem3205094 A s t). Qed.
Lemma lem3205096 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term2 A s t) = ((@INTER A s t) = (term3 A s t)).
Proof. exact (eq_refl (term2 A s t)). Qed.
Lemma lem3205122 {_83095 : Type'} : term4 _83095.
Proof. exact (EQ_MP (@lem3184739 _83095) (@lem3184736 _83095)). Qed.
Lemma lem3205123 {_83095 : Type'} (p : _83095 -> Prop) : term5 _83095 p.
Proof. exact (@lem3205122 _83095 p). Qed.
Lemma lem3205124 {_83095 : Type'} (p : _83095 -> Prop) : (term5 _83095 p) = (term6 _83095 p).
Proof. exact (eq_refl (term5 _83095 p)). Qed.
Lemma lem3205125 {_83095 : Type'} (p : _83095 -> Prop) : term6 _83095 p.
Proof. exact (EQ_MP (@lem3205124 _83095 p) (@lem3205123 _83095 p)). Qed.
Lemma lem3205126 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : term7 _83095 p x.
Proof. exact (@lem3205125 _83095 p x). Qed.
Lemma lem3205127 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term7 _83095 p x) = ((term8 _83095 x p) = (p x)).
Proof. exact (eq_refl (term7 _83095 p x)). Qed.
Lemma lem3205151 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@INTER A s t) = (term3 A s t).
Proof. exact (EQ_MP (@lem3205096 A s t) (@lem3205095 A s t)). Qed.
Lemma lem3205152 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@INTER A s t) = (term3 A s t).
Proof. exact (@lem3205151 A s t). Qed.
Lemma lem3205159 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem3205160 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term9 A x s t) = (term10 A x s t).
Proof. exact (MK_COMB (@lem3205159 A x) (@lem3205152 A s t)). Qed.
Lemma lem3205162 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term8 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem3205127 _83095 p x) (@lem3205126 _83095 p x)). Qed.
Lemma lem3205163 {A : Type'} (p : A -> Prop) (x : A) : (term8 A x p) = (p x).
Proof. exact (@lem3205162 A p x). Qed.
Lemma lem3205164 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term11 A x s t) = (term12 A s t x).
Proof. exact (@lem3205163 A (term13 A s t) x). Qed.
Lemma lem3205165 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term12 A s t x) = (term14 A s x t).
Proof. exact (eq_refl (term12 A s t x)). Qed.
Lemma lem3205166 {A : Type'} (GEN_PVAR_2 : A) : (@SETSPEC A GEN_PVAR_2) = (@SETSPEC A GEN_PVAR_2).
Proof. exact (eq_refl (@SETSPEC A GEN_PVAR_2)). Qed.
Lemma lem3205167 {A : Type'} (GEN_PVAR_2 : A) (s : A -> Prop) (x : A) (t : A -> Prop) : (term15 A GEN_PVAR_2 s t x) = (term16 A GEN_PVAR_2 s x t).
Proof. exact (MK_COMB (@lem3205166 A GEN_PVAR_2) (@lem3205165 A s x t)). Qed.
Lemma lem3205168 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3205169 {A : Type'} (GEN_PVAR_2 : A) (s : A -> Prop) (t : A -> Prop) (x : A) : (term17 A GEN_PVAR_2 s t x) = (term18 A GEN_PVAR_2 s t x).
Proof. exact (MK_COMB (@lem3205167 A GEN_PVAR_2 s x t) (@lem3205168 A x)). Qed.
Lemma lem3205170 {A : Type'} (GEN_PVAR_2 : A) (s : A -> Prop) (t : A -> Prop) : (term19 A GEN_PVAR_2 s t) = (term20 A GEN_PVAR_2 s t).
Proof. exact (fun_ext (fun x : A => @lem3205169 A GEN_PVAR_2 s t x)). Qed.
Lemma lem3205171 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3205172 {A : Type'} (GEN_PVAR_2 : A) (s : A -> Prop) (t : A -> Prop) : (term21 A GEN_PVAR_2 s t) = (term22 A GEN_PVAR_2 s t).
Proof. exact (MK_COMB (@lem3205171 A) (@lem3205170 A GEN_PVAR_2 s t)). Qed.
Lemma lem3205173 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term23 A s t) = (term24 A s t).
Proof. exact (fun_ext (fun GEN_PVAR_2 : A => @lem3205172 A GEN_PVAR_2 s t)). Qed.
Lemma lem3205174 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem3205175 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term25 A s t) = (term3 A s t).
Proof. exact (MK_COMB (@lem3205174 A) (@lem3205173 A s t)). Qed.
Lemma lem3205176 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem3205177 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term11 A x s t) = (term10 A x s t).
Proof. exact (MK_COMB (@lem3205176 A x) (@lem3205175 A s t)). Qed.
Lemma lem3205178 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3205179 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term26 A x s t) = (term27 A x s t).
Proof. exact (MK_COMB (@lem3205178) (@lem3205177 A x s t)). Qed.
Lemma lem3205180 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term12 A s t x) = (term14 A s x t).
Proof. exact (eq_refl (term12 A s t x)). Qed.
Lemma lem3205181 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : ((term11 A x s t) = (term12 A s t x)) = ((term10 A x s t) = (term14 A s x t)).
Proof. exact (MK_COMB (@lem3205179 A x s t) (@lem3205180 A s x t)). Qed.
Lemma lem3205182 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term10 A x s t) = (term14 A s x t).
Proof. exact (EQ_MP (@lem3205181 A s x t) (@lem3205164 A s t x)). Qed.
Lemma lem3205185 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term9 A x s t) = (term14 A s x t).
Proof. exact (TRANS (@lem3205160 A x s t) (@lem3205182 A s x t)). Qed.
Lemma lem3205186 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3205187 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term28 A x s t) = (term29 A s x t).
Proof. exact (MK_COMB (@lem3205186) (@lem3205185 A s x t)). Qed.
Lemma lem3205190 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term14 A s x t) = (term14 A s x t).
Proof. exact (eq_refl (term14 A s x t)). Qed.
Lemma lem3205191 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : ((term9 A x s t) = (term14 A s x t)) = ((term14 A s x t) = (term14 A s x t)).
Proof. exact (MK_COMB (@lem3205187 A s x t) (@lem3205190 A s x t)). Qed.
Lemma lem3205193 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3205194 (x : Prop) : (x = x) = True.
Proof. exact (@lem3205193 Prop x). Qed.
Lemma lem3205195 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : ((term14 A s x t) = (term14 A s x t)) = True.
Proof. exact (@lem3205194 (term14 A s x t)). Qed.
Lemma lem3205196 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : ((term9 A x s t) = (term14 A s x t)) = True.
Proof. exact (TRANS (@lem3205191 A s x t) (@lem3205195 A s x t)). Qed.
Lemma lem3205197 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term30 A s t) = (term31 A).
Proof. exact (fun_ext (fun x : A => @lem3205196 A s x t)). Qed.
Lemma lem3205198 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3205199 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term32 A s t) = (term33 A).
Proof. exact (MK_COMB (@lem3205198 A) (@lem3205197 A s t)). Qed.
Lemma lem3205201 {A : Type'} (t : Prop) : (term34 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3205202 {A : Type'} (t : Prop) : (term34 A t) = t.
Proof. exact (@lem3205201 A t). Qed.
Lemma lem3205203 {A : Type'} : (term33 A) = True.
Proof. exact (@lem3205202 A True). Qed.
Lemma lem3205204 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term32 A s t) = True.
Proof. exact (TRANS (@lem3205199 A s t) (@lem3205203 A)). Qed.
Lemma lem3205205 {A : Type'} (s : A -> Prop) : (term35 A s) = (term36 A).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3205204 A s t)). Qed.
Lemma lem3205206 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3205207 {A : Type'} (s : A -> Prop) : (term37 A s) = (term38 A).
Proof. exact (MK_COMB (@lem3205206 A) (@lem3205205 A s)). Qed.
Lemma lem3205209 {A : Type'} (t : Prop) : (term34 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3205210 {A : Type'} (t : Prop) : (term39 A t) = t.
Proof. exact (@lem3205209 (A -> Prop) t). Qed.
Lemma lem3205211 {A : Type'} : (term38 A) = True.
Proof. exact (@lem3205210 A True). Qed.
Lemma lem3205212 {A : Type'} (s : A -> Prop) : (term37 A s) = True.
Proof. exact (TRANS (@lem3205207 A s) (@lem3205211 A)). Qed.
Lemma lem3205213 {A : Type'} : (term40 A) = (term36 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3205212 A s)). Qed.
Lemma lem3205214 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3205215 {A : Type'} : (term41 A) = (term38 A).
Proof. exact (MK_COMB (@lem3205214 A) (@lem3205213 A)). Qed.
Lemma lem3205217 {A : Type'} (t : Prop) : (term34 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3205218 {A : Type'} (t : Prop) : (term39 A t) = t.
Proof. exact (@lem3205217 (A -> Prop) t). Qed.
Lemma lem3205219 {A : Type'} : (term38 A) = True.
Proof. exact (@lem3205218 A True). Qed.
Lemma lem3205220 {A : Type'} : (term41 A) = True.
Proof. exact (TRANS (@lem3205215 A) (@lem3205219 A)). Qed.
Lemma lem3205221 {A : Type'} : True = (term41 A).
Proof. exact (SYM (@lem3205220 A)). Qed.
Lemma lem3205222 {A : Type'} : term41 A.
Proof. exact (EQ_MP (@lem3205221 A) (@lem0)). Qed.
