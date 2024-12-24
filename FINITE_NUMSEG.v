Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FINITE_NUMSEG_term_abbrevs.
Require Import FINITE_NUMSEG_LE_spec.
Require Import FINITE_SUBSET_spec.
Require Import SUBSET_spec.
Require Import numseg_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1842_spec.
Require Import thm3184736_spec.
Require Import thm3184739_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Lemma lem5329078 (m : nat) : term0 m.
Proof. exact (@lem5329077 m). Qed.
Lemma lem5329079 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem5329080 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem5329079 m) (@lem5329078 m)). Qed.
Lemma lem5329081 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem5329080 m n). Qed.
Lemma lem5329082 (m : nat) (n : nat) : (term2 m n) = ((dotdot m n) = (term3 m n)).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem5329108 {_83095 : Type'} : term4 _83095.
Proof. exact (EQ_MP (@lem3184739 _83095) (@lem3184736 _83095)). Qed.
Lemma lem5329109 {_83095 : Type'} (p : _83095 -> Prop) : term5 _83095 p.
Proof. exact (@lem5329108 _83095 p). Qed.
Lemma lem5329110 {_83095 : Type'} (p : _83095 -> Prop) : (term5 _83095 p) = (term6 _83095 p).
Proof. exact (eq_refl (term5 _83095 p)). Qed.
Lemma lem5329111 {_83095 : Type'} (p : _83095 -> Prop) : term6 _83095 p.
Proof. exact (EQ_MP (@lem5329110 _83095 p) (@lem5329109 _83095 p)). Qed.
Lemma lem5329112 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : term7 _83095 p x.
Proof. exact (@lem5329111 _83095 p x). Qed.
Lemma lem5329113 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term7 _83095 p x) = ((term8 _83095 x p) = (p x)).
Proof. exact (eq_refl (term7 _83095 p x)). Qed.
Lemma lem5329122 {A : Type'} (s : A -> Prop) : term9 A s.
Proof. exact (@lem3194148 A s). Qed.
Lemma lem5329123 {A : Type'} (s : A -> Prop) : (term9 A s) = (term10 A s).
Proof. exact (eq_refl (term9 A s)). Qed.
Lemma lem5329124 {A : Type'} (s : A -> Prop) : term10 A s.
Proof. exact (EQ_MP (@lem5329123 A s) (@lem5329122 A s)). Qed.
Lemma lem5329125 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term11 A s t.
Proof. exact (@lem5329124 A s t). Qed.
Lemma lem5329126 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term11 A s t) = ((@SUBSET A s t) = (term12 A s t)).
Proof. exact (eq_refl (term11 A s t)). Qed.
Lemma lem5329128 (n : nat) : term13 n.
Proof. exact (@lem4621993 n). Qed.
Lemma lem5329129 (n : nat) : (term13 n) = (term14 n).
Proof. exact (eq_refl (term13 n)). Qed.
Lemma lem5329130 (n : nat) : term14 n.
Proof. exact (EQ_MP (@lem5329129 n) (@lem5329128 n)). Qed.
Lemma lem5329131 (n : nat) : (term14 n) = ((term14 n) = True).
Proof. exact (@lem7 (term14 n)). Qed.
Lemma lem5329133 {A : Type'} (h1 : term15 A) : term15 A.
Proof. exact (h1). Qed.
Lemma lem5329134 {A : Type'} (s : A -> Prop) (h1 : term15 A) : term16 A s.
Proof. exact (@lem5329133 A h1 s). Qed.
Lemma lem5329135 {A : Type'} (s : A -> Prop) : (term16 A s) = (term17 A s).
Proof. exact (eq_refl (term16 A s)). Qed.
Lemma lem5329136 {A : Type'} (s : A -> Prop) (h1 : term15 A) : term17 A s.
Proof. exact (EQ_MP (@lem5329135 A s) (@lem5329134 A s h1)). Qed.
Lemma lem5329137 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term15 A) : term18 A s t.
Proof. exact (@lem5329136 A s h1 t). Qed.
Lemma lem5329138 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term18 A s t) = (term19 A t s).
Proof. exact (eq_refl (term18 A s t)). Qed.
Lemma lem5329139 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : term15 A) : term19 A t s.
Proof. exact (EQ_MP (@lem5329138 A t s) (@lem5329137 A s t h1)). Qed.
Lemma lem5329140 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term20 A s t) : term20 A s t.
Proof. exact (h1). Qed.
Lemma lem5329141 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term15 A) (h2 : term20 A s t) : @FINITE A s.
Proof. exact (@lem5329139 A t s h1 (@lem5329140 A s t h2)). Qed.
Lemma lem5329142 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term20 A s t) : term21 A s.
Proof. exact (fun h0 : term15 A => @lem5329141 A s t h0 h1). Qed.
Lemma lem5329143 {A : Type'} (s : A -> Prop) (h1 : term22 A s) : term22 A s.
Proof. exact (h1). Qed.
Lemma lem5329144 {A : Type'} (s : A -> Prop) (h1 : term22 A s) : term21 A s.
Proof. exact (ex_elim (@lem5329143 A s h1) (fun t : A -> Prop => fun h0 : term23 A s t => @lem5329142 A s t h0)). Qed.
Lemma lem5329145 {A : Type'} (h1 : term15 A) : term15 A.
Proof. exact (h1). Qed.
Lemma lem5329146 {A : Type'} (s : A -> Prop) (h1 : term15 A) (h2 : term22 A s) : @FINITE A s.
Proof. exact (@lem5329144 A s h2 (@lem5329145 A h1)). Qed.
Lemma lem5329147 {A : Type'} (s : A -> Prop) (h1 : term15 A) : term24 A s.
Proof. exact (fun h0 : term22 A s => @lem5329146 A s h1 h0). Qed.
Lemma lem5329148 {A : Type'} (h1 : term15 A) : term25 A.
Proof. exact (fun s : A -> Prop => @lem5329147 A s h1). Qed.
Lemma lem5329149 {A : Type'} : term26 A.
Proof. exact (fun h0 : term15 A => @lem5329148 A h0). Qed.
Lemma lem5329150 {A : Type'} : term25 A.
Proof. exact (@lem5329149 A (@lem3599924 A)). Qed.
Lemma lem5329151 {A : Type'} (s : A -> Prop) : term27 A s.
Proof. exact (@lem5329150 A s). Qed.
Lemma lem5329152 {A : Type'} (s : A -> Prop) : (term27 A s) = (term24 A s).
Proof. exact (eq_refl (term27 A s)). Qed.
Lemma lem5329155 {A : Type'} (s : A -> Prop) : term24 A s.
Proof. exact (EQ_MP (@lem5329152 A s) (@lem5329151 A s)). Qed.
Lemma lem5329156 (s : nat -> Prop) : term28 s.
Proof. exact (@lem5329155 nat s). Qed.
Lemma lem5329157 (m : nat) (n : nat) : term29 m n.
Proof. exact (@lem5329156 (dotdot m n)). Qed.
Lemma lem5329161 (n : nat) : (term14 n) = True.
Proof. exact (EQ_MP (@lem5329131 n) (@lem5329130 n)). Qed.
Lemma lem5329162 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5329163 (n : nat) : (term30 n) = (and True).
Proof. exact (MK_COMB (@lem5329162) (@lem5329161 n)). Qed.
Lemma lem5329168 (m : nat) (n : nat) : (term31 m n) = (term31 m n).
Proof. exact (eq_refl (term31 m n)). Qed.
Lemma lem5329169 (m : nat) (n : nat) : (term32 m n) = (term33 m n).
Proof. exact (MK_COMB (@lem5329163 n) (@lem5329168 m n)). Qed.
Lemma lem5329171 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem5329172 (m : nat) (n : nat) : (term33 m n) = (term31 m n).
Proof. exact (@lem5329171 (term31 m n)). Qed.
Lemma lem5329177 (m : nat) (n : nat) : (term32 m n) = (term31 m n).
Proof. exact (TRANS (@lem5329169 m n) (@lem5329172 m n)). Qed.
Lemma lem5329178 (m : nat) (n : nat) : (term31 m n) = (term32 m n).
Proof. exact (SYM (@lem5329177 m n)). Qed.
Lemma lem5329180 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term12 A s t).
Proof. exact (EQ_MP (@lem5329126 A s t) (@lem5329125 A s t)). Qed.
Lemma lem5329181 (s : nat -> Prop) (t : nat -> Prop) : (@SUBSET nat s t) = (term34 s t).
Proof. exact (@lem5329180 nat s t). Qed.
Lemma lem5329182 (m : nat) (n : nat) : (term31 m n) = (term35 m n).
Proof. exact (@lem5329181 (dotdot m n) (term36 n)). Qed.
Lemma lem5329190 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term37 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem5329191 (p : Prop) (q : Prop) (p' : Prop) : term38 p q p'.
Proof. exact (fun q' : Prop => @lem5329190 p q p' q'). Qed.
Lemma lem5329192 (p : Prop) (q : Prop) : term39 p q.
Proof. exact (fun p' : Prop => @lem5329191 p q p'). Qed.
Lemma lem5329193 (m : nat) (x : nat) (n : nat) : term40 m x n.
Proof. exact (@lem5329192 (term41 x m n) (term42 x n)). Qed.
Lemma lem5329194 (m : nat) (x : nat) (n : nat) (p' : Prop) : term43 m x n p'.
Proof. exact (@lem5329193 m x n p'). Qed.
Lemma lem5329195 (m : nat) (x : nat) (n : nat) (p' : Prop) : (term43 m x n p') = (term44 m x n p').
Proof. exact (eq_refl (term43 m x n p')). Qed.
Lemma lem5329196 (m : nat) (x : nat) (n : nat) (p' : Prop) : term44 m x n p'.
Proof. exact (EQ_MP (@lem5329195 m x n p') (@lem5329194 m x n p')). Qed.
Lemma lem5329197 (m : nat) (x : nat) (n : nat) (p' : Prop) (q' : Prop) : term45 m x n p' q'.
Proof. exact (@lem5329196 m x n p' q'). Qed.
Lemma lem5329198 (m : nat) (x : nat) (n : nat) (p' : Prop) (q' : Prop) : (term45 m x n p' q') = (term46 m x n p' q').
Proof. exact (eq_refl (term45 m x n p' q')). Qed.
Lemma lem5329199 (m : nat) (x : nat) (n : nat) (p' : Prop) (q' : Prop) : term46 m x n p' q'.
Proof. exact (EQ_MP (@lem5329198 m x n p' q') (@lem5329197 m x n p' q')). Qed.
Lemma lem5329201 (m : nat) (n : nat) : (dotdot m n) = (term3 m n).
Proof. exact (EQ_MP (@lem5329082 m n) (@lem5329081 m n)). Qed.
Lemma lem5329208 (x : nat) : (@IN nat x) = (@IN nat x).
Proof. exact (eq_refl (@IN nat x)). Qed.
Lemma lem5329209 (x : nat) (m : nat) (n : nat) : (term41 x m n) = (term47 x m n).
Proof. exact (MK_COMB (@lem5329208 x) (@lem5329201 m n)). Qed.
Lemma lem5329211 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term8 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem5329113 _83095 p x) (@lem5329112 _83095 p x)). Qed.
Lemma lem5329212 (p : nat -> Prop) (x : nat) : (term48 x p) = (p x).
Proof. exact (@lem5329211 nat p x). Qed.
Lemma lem5329213 (m : nat) (n : nat) (x : nat) : (term49 x m n) = (term50 m n x).
Proof. exact (@lem5329212 (term51 m n) x). Qed.
Lemma lem5329214 (m : nat) (x : nat) (n : nat) : (term50 m n x) = (term52 m x n).
Proof. exact (eq_refl (term50 m n x)). Qed.
Lemma lem5329215 (GEN_PVAR_229 : nat) : (@SETSPEC nat GEN_PVAR_229) = (@SETSPEC nat GEN_PVAR_229).
Proof. exact (eq_refl (@SETSPEC nat GEN_PVAR_229)). Qed.
Lemma lem5329216 (GEN_PVAR_229 : nat) (m : nat) (x : nat) (n : nat) : (term53 GEN_PVAR_229 m n x) = (term54 GEN_PVAR_229 m x n).
Proof. exact (MK_COMB (@lem5329215 GEN_PVAR_229) (@lem5329214 m x n)). Qed.
Lemma lem5329217 (x : nat) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5329218 (GEN_PVAR_229 : nat) (m : nat) (n : nat) (x : nat) : (term55 GEN_PVAR_229 m n x) = (term56 GEN_PVAR_229 m n x).
Proof. exact (MK_COMB (@lem5329216 GEN_PVAR_229 m x n) (@lem5329217 x)). Qed.
Lemma lem5329219 (GEN_PVAR_229 : nat) (m : nat) (n : nat) : (term57 GEN_PVAR_229 m n) = (term58 GEN_PVAR_229 m n).
Proof. exact (fun_ext (fun x : nat => @lem5329218 GEN_PVAR_229 m n x)). Qed.
Lemma lem5329220 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem5329221 (GEN_PVAR_229 : nat) (m : nat) (n : nat) : (term59 GEN_PVAR_229 m n) = (term60 GEN_PVAR_229 m n).
Proof. exact (MK_COMB (@lem5329220) (@lem5329219 GEN_PVAR_229 m n)). Qed.
Lemma lem5329222 (m : nat) (n : nat) : (term61 m n) = (term62 m n).
Proof. exact (fun_ext (fun GEN_PVAR_229 : nat => @lem5329221 GEN_PVAR_229 m n)). Qed.
Lemma lem5329223 : (@GSPEC nat) = (@GSPEC nat).
Proof. exact (eq_refl (@GSPEC nat)). Qed.
Lemma lem5329224 (m : nat) (n : nat) : (term63 m n) = (term3 m n).
Proof. exact (MK_COMB (@lem5329223) (@lem5329222 m n)). Qed.
Lemma lem5329225 (x : nat) : (@IN nat x) = (@IN nat x).
Proof. exact (eq_refl (@IN nat x)). Qed.
Lemma lem5329226 (x : nat) (m : nat) (n : nat) : (term49 x m n) = (term47 x m n).
Proof. exact (MK_COMB (@lem5329225 x) (@lem5329224 m n)). Qed.
Lemma lem5329227 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5329228 (x : nat) (m : nat) (n : nat) : (term64 x m n) = (term65 x m n).
Proof. exact (MK_COMB (@lem5329227) (@lem5329226 x m n)). Qed.
Lemma lem5329229 (m : nat) (x : nat) (n : nat) : (term50 m n x) = (term52 m x n).
Proof. exact (eq_refl (term50 m n x)). Qed.
Lemma lem5329230 (m : nat) (x : nat) (n : nat) : ((term49 x m n) = (term50 m n x)) = ((term47 x m n) = (term52 m x n)).
Proof. exact (MK_COMB (@lem5329228 x m n) (@lem5329229 m x n)). Qed.
Lemma lem5329231 (m : nat) (x : nat) (n : nat) : (term47 x m n) = (term52 m x n).
Proof. exact (EQ_MP (@lem5329230 m x n) (@lem5329213 m n x)). Qed.
Lemma lem5329234 (m : nat) (x : nat) (n : nat) : (term41 x m n) = (term52 m x n).
Proof. exact (TRANS (@lem5329209 x m n) (@lem5329231 m x n)). Qed.
Lemma lem5329235 (m : nat) (x : nat) (n : nat) (q' : Prop) : term66 m x n q'.
Proof. exact (@lem5329199 m x n (term52 m x n) q'). Qed.
Lemma lem5329236 (m : nat) (x : nat) (n : nat) (q' : Prop) : term67 m x n q'.
Proof. exact (@lem5329235 m x n q' (@lem5329234 m x n)). Qed.
Lemma lem5329237 (m : nat) (x : nat) (n : nat) (h1 : term52 m x n) : term52 m x n.
Proof. exact (h1). Qed.
Lemma lem5329238 (m : nat) (x : nat) (n : nat) (h1 : term52 m x n) : Peano.le x n.
Proof. exact (proj2 (@lem5329237 m x n h1)). Qed.
Lemma lem5329239 (x : nat) (n : nat) : (Peano.le x n) = ((Peano.le x n) = True).
Proof. exact (@lem7 (Peano.le x n)). Qed.
Lemma lem5329245 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term8 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem5329113 _83095 p x) (@lem5329112 _83095 p x)). Qed.
Lemma lem5329246 (p : nat -> Prop) (x : nat) : (term48 x p) = (p x).
Proof. exact (@lem5329245 nat p x). Qed.
Lemma lem5329247 (n : nat) (x : nat) : (term68 x n) = (term69 n x).
Proof. exact (@lem5329246 (term70 n) x). Qed.
Lemma lem5329248 (x : nat) (n : nat) : (term69 n x) = (Peano.le x n).
Proof. exact (eq_refl (term69 n x)). Qed.
Lemma lem5329249 (GEN_PVAR_230 : nat) : (@SETSPEC nat GEN_PVAR_230) = (@SETSPEC nat GEN_PVAR_230).
Proof. exact (eq_refl (@SETSPEC nat GEN_PVAR_230)). Qed.
Lemma lem5329250 (GEN_PVAR_230 : nat) (x : nat) (n : nat) : (term71 GEN_PVAR_230 n x) = (term72 GEN_PVAR_230 x n).
Proof. exact (MK_COMB (@lem5329249 GEN_PVAR_230) (@lem5329248 x n)). Qed.
Lemma lem5329251 (x : nat) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5329252 (GEN_PVAR_230 : nat) (n : nat) (x : nat) : (term73 GEN_PVAR_230 n x) = (term74 GEN_PVAR_230 n x).
Proof. exact (MK_COMB (@lem5329250 GEN_PVAR_230 x n) (@lem5329251 x)). Qed.
Lemma lem5329253 (GEN_PVAR_230 : nat) (n : nat) : (term75 GEN_PVAR_230 n) = (term76 GEN_PVAR_230 n).
Proof. exact (fun_ext (fun x : nat => @lem5329252 GEN_PVAR_230 n x)). Qed.
Lemma lem5329254 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem5329255 (GEN_PVAR_230 : nat) (n : nat) : (term77 GEN_PVAR_230 n) = (term78 GEN_PVAR_230 n).
Proof. exact (MK_COMB (@lem5329254) (@lem5329253 GEN_PVAR_230 n)). Qed.
Lemma lem5329256 (n : nat) : (term79 n) = (term80 n).
Proof. exact (fun_ext (fun GEN_PVAR_230 : nat => @lem5329255 GEN_PVAR_230 n)). Qed.
Lemma lem5329257 : (@GSPEC nat) = (@GSPEC nat).
Proof. exact (eq_refl (@GSPEC nat)). Qed.
Lemma lem5329258 (n : nat) : (term81 n) = (term36 n).
Proof. exact (MK_COMB (@lem5329257) (@lem5329256 n)). Qed.
Lemma lem5329259 (x : nat) : (@IN nat x) = (@IN nat x).
Proof. exact (eq_refl (@IN nat x)). Qed.
Lemma lem5329260 (x : nat) (n : nat) : (term68 x n) = (term42 x n).
Proof. exact (MK_COMB (@lem5329259 x) (@lem5329258 n)). Qed.
Lemma lem5329261 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5329262 (x : nat) (n : nat) : (term82 x n) = (term83 x n).
Proof. exact (MK_COMB (@lem5329261) (@lem5329260 x n)). Qed.
Lemma lem5329263 (x : nat) (n : nat) : (term69 n x) = (Peano.le x n).
Proof. exact (eq_refl (term69 n x)). Qed.
Lemma lem5329264 (x : nat) (n : nat) : ((term68 x n) = (term69 n x)) = ((term42 x n) = (Peano.le x n)).
Proof. exact (MK_COMB (@lem5329262 x n) (@lem5329263 x n)). Qed.
Lemma lem5329265 (x : nat) (n : nat) : (term42 x n) = (Peano.le x n).
Proof. exact (EQ_MP (@lem5329264 x n) (@lem5329247 n x)). Qed.
Lemma lem5329267 (m : nat) (x : nat) (n : nat) (h1 : term52 m x n) : (Peano.le x n) = True.
Proof. exact (EQ_MP (@lem5329239 x n) (@lem5329238 m x n h1)). Qed.
Lemma lem5329268 (m : nat) (x : nat) (n : nat) (h1 : term52 m x n) : (term42 x n) = True.
Proof. exact (TRANS (@lem5329265 x n) (@lem5329267 m x n h1)). Qed.
Lemma lem5329269 (m : nat) (x : nat) (n : nat) : term84 m x n.
Proof. exact (fun h0 : term52 m x n => @lem5329268 m x n h0). Qed.
Lemma lem5329270 (m : nat) (x : nat) (n : nat) : term85 m x n.
Proof. exact (@lem5329236 m x n True). Qed.
Lemma lem5329271 (m : nat) (x : nat) (n : nat) : (term86 m x n) = (term87 m x n).
Proof. exact (@lem5329270 m x n (@lem5329269 m x n)). Qed.
Lemma lem5329273 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem5329274 (m : nat) (x : nat) (n : nat) : (term87 m x n) = True.
Proof. exact (@lem5329273 (term52 m x n)). Qed.
Lemma lem5329275 (m : nat) (x : nat) (n : nat) : (term86 m x n) = True.
Proof. exact (TRANS (@lem5329271 m x n) (@lem5329274 m x n)). Qed.
Lemma lem5329276 (m : nat) (n : nat) : (term88 m n) = term89.
Proof. exact (fun_ext (fun x : nat => @lem5329275 m x n)). Qed.
Lemma lem5329277 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5329278 (m : nat) (n : nat) : (term35 m n) = term90.
Proof. exact (MK_COMB (@lem5329277) (@lem5329276 m n)). Qed.
Lemma lem5329280 {A : Type'} (t : Prop) : (term91 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem5329281 (t : Prop) : (term92 t) = t.
Proof. exact (@lem5329280 nat t). Qed.
Lemma lem5329282 : term90 = True.
Proof. exact (@lem5329281 True). Qed.
Lemma lem5329283 (m : nat) (n : nat) : (term35 m n) = True.
Proof. exact (TRANS (@lem5329278 m n) (@lem5329282)). Qed.
Lemma lem5329284 (m : nat) (n : nat) : (term31 m n) = True.
Proof. exact (TRANS (@lem5329182 m n) (@lem5329283 m n)). Qed.
Lemma lem5329285 (m : nat) (n : nat) : True = (term31 m n).
Proof. exact (SYM (@lem5329284 m n)). Qed.
Lemma lem5329286 (m : nat) (n : nat) : term31 m n.
Proof. exact (EQ_MP (@lem5329285 m n) (@lem0)). Qed.
Lemma lem5329287 (m : nat) (n : nat) : term32 m n.
Proof. exact (EQ_MP (@lem5329178 m n) (@lem5329286 m n)). Qed.
Lemma lem5329288 (m : nat) (n : nat) : term93 m n.
Proof. exact (ex_intro (term94 m n) (term36 n) (@lem5329287 m n)). Qed.
Lemma lem5329289 (m : nat) (n : nat) : term95 m n.
Proof. exact (@lem5329157 m n (@lem5329288 m n)). Qed.
Lemma lem5329294 (m : nat) : term96 m.
Proof. exact (fun n : nat => @lem5329289 m n). Qed.
Lemma lem5329299 : term97.
Proof. exact (fun m : nat => @lem5329294 m). Qed.
