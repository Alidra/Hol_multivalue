Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUM_EQ_term_abbrevs.
Require Import ITERATE_EQ_spec.
Require Import MONOIDAL_REAL_ADD_spec.
Require Import thm0_spec.
Require Import thm7_spec.
Require Import thm7064097_spec.
Require Import thm7064111_spec.
Lemma lem7081143 : (@monoidal real real_add) = ((@monoidal real real_add) = True).
Proof. exact (@lem7 (@monoidal real real_add)). Qed.
Lemma lem7081145 {A B : Type'} (h1 : term0 A B) : term0 A B.
Proof. exact (h1). Qed.
Lemma lem7081146 {A B : Type'} (op : type1400 B) (h1 : term0 A B) : term1 A B op.
Proof. exact (@lem7081145 A B h1 op). Qed.
Lemma lem7081147 {A B : Type'} (op : type1400 B) : (term1 A B op) = (term2 A B op).
Proof. exact (eq_refl (term1 A B op)). Qed.
Lemma lem7081148 {A B : Type'} (op : type1400 B) (h1 : term0 A B) : term2 A B op.
Proof. exact (EQ_MP (@lem7081147 A B op) (@lem7081146 A B op h1)). Qed.
Lemma lem7081149 {B : Type'} (op : type1400 B) (h1 : @monoidal B op) : @monoidal B op.
Proof. exact (h1). Qed.
Lemma lem7081150 {A B : Type'} (op : type1400 B) (h1 : term0 A B) (h2 : @monoidal B op) : term3 A B op.
Proof. exact (@lem7081148 A B op h1 (@lem7081149 B op h2)). Qed.
Lemma lem7081151 {A B : Type'} (op : type1400 B) (h1 : @monoidal B op) : term4 A B op.
Proof. exact (fun h0 : term0 A B => @lem7081150 A B op h0 h1). Qed.
Lemma lem7081152 {A B : Type'} (h1 : term0 A B) : term0 A B.
Proof. exact (h1). Qed.
Lemma lem7081153 {A B : Type'} (op : type1400 B) (h1 : term0 A B) (h2 : @monoidal B op) : term3 A B op.
Proof. exact (@lem7081151 A B op h2 (@lem7081152 A B h1)). Qed.
Lemma lem7081154 {A B : Type'} (op : type1400 B) (h1 : term0 A B) : term2 A B op.
Proof. exact (fun h0 : @monoidal B op => @lem7081153 A B op h1 h0). Qed.
Lemma lem7081155 {A B : Type'} (h1 : term0 A B) : term0 A B.
Proof. exact (fun op : type1400 B => @lem7081154 A B op h1). Qed.
Lemma lem7081156 {A B : Type'} : term5 A B.
Proof. exact (fun h0 : term0 A B => @lem7081155 A B h0). Qed.
Lemma lem7081157 {A B : Type'} : term0 A B.
Proof. exact (@lem7081156 A B (@lem5985778 A B)). Qed.
Lemma lem7081158 {A B : Type'} (op : type1400 B) : term1 A B op.
Proof. exact (@lem7081157 A B op). Qed.
Lemma lem7081159 {A B : Type'} (op : type1400 B) : (term1 A B op) = (term2 A B op).
Proof. exact (eq_refl (term1 A B op)). Qed.
Lemma lem7081186 {_131408 : Type'} : (@sum _131408) = (@iterate real _131408 real_add).
Proof. exact (TRANS (@lem7064097 _131408) (@lem7064111 _131408)). Qed.
Lemma lem7081187 {_132349 : Type'} : (@sum _132349) = (@iterate real _132349 real_add).
Proof. exact (@lem7081186 _132349). Qed.
Lemma lem7081188 {_132349 : Type'} (s : _132349 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7081189 {_132349 : Type'} (s : _132349 -> Prop) : (@sum _132349 s) = (@iterate real _132349 real_add s).
Proof. exact (MK_COMB (@lem7081187 _132349) (@lem7081188 _132349 s)). Qed.
Lemma lem7081190 {_132349 : Type'} (f : _132349 -> real) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7081191 {_132349 : Type'} (s : _132349 -> Prop) (f : _132349 -> real) : (@sum _132349 s f) = (@iterate real _132349 real_add s f).
Proof. exact (MK_COMB (@lem7081189 _132349 s) (@lem7081190 _132349 f)). Qed.
Lemma lem7081192 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7081193 {_132349 : Type'} (s : _132349 -> Prop) (f : _132349 -> real) : (term6 _132349 s f) = (term7 _132349 s f).
Proof. exact (MK_COMB (@lem7081192) (@lem7081191 _132349 s f)). Qed.
Lemma lem7081195 {_131408 : Type'} : (@sum _131408) = (@iterate real _131408 real_add).
Proof. exact (TRANS (@lem7064097 _131408) (@lem7064111 _131408)). Qed.
Lemma lem7081196 {_132349 : Type'} : (@sum _132349) = (@iterate real _132349 real_add).
Proof. exact (@lem7081195 _132349). Qed.
Lemma lem7081197 {_132349 : Type'} (s : _132349 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7081198 {_132349 : Type'} (s : _132349 -> Prop) : (@sum _132349 s) = (@iterate real _132349 real_add s).
Proof. exact (MK_COMB (@lem7081196 _132349) (@lem7081197 _132349 s)). Qed.
Lemma lem7081199 {_132349 : Type'} (g : _132349 -> real) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem7081200 {_132349 : Type'} (s : _132349 -> Prop) (g : _132349 -> real) : (@sum _132349 s g) = (@iterate real _132349 real_add s g).
Proof. exact (MK_COMB (@lem7081198 _132349 s) (@lem7081199 _132349 g)). Qed.
Lemma lem7081201 {_132349 : Type'} (f : _132349 -> real) (s : _132349 -> Prop) (g : _132349 -> real) : ((@sum _132349 s f) = (@sum _132349 s g)) = ((@iterate real _132349 real_add s f) = (@iterate real _132349 real_add s g)).
Proof. exact (MK_COMB (@lem7081193 _132349 s f) (@lem7081200 _132349 s g)). Qed.
Lemma lem7081204 {_132349 : Type'} (s : _132349 -> Prop) (f : _132349 -> real) (g : _132349 -> real) : (term8 _132349 s f g) = (term8 _132349 s f g).
Proof. exact (eq_refl (term8 _132349 s f g)). Qed.
Lemma lem7081205 {_132349 : Type'} (f : _132349 -> real) (s : _132349 -> Prop) (g : _132349 -> real) : (term9 _132349 f s g) = (term10 _132349 f s g).
Proof. exact (MK_COMB (@lem7081204 _132349 s f g) (@lem7081201 _132349 f s g)). Qed.
Lemma lem7081208 {_132349 : Type'} (f : _132349 -> real) (g : _132349 -> real) : (term11 _132349 f g) = (term12 _132349 f g).
Proof. exact (fun_ext (fun s : _132349 -> Prop => @lem7081205 _132349 f s g)). Qed.
Lemma lem7081209 {_132349 : Type'} : (@all (_132349 -> Prop)) = (@all (_132349 -> Prop)).
Proof. exact (eq_refl (@all (_132349 -> Prop))). Qed.
Lemma lem7081210 {_132349 : Type'} (f : _132349 -> real) (g : _132349 -> real) : (term13 _132349 f g) = (term14 _132349 f g).
Proof. exact (MK_COMB (@lem7081209 _132349) (@lem7081208 _132349 f g)). Qed.
Lemma lem7081215 {_132349 : Type'} (f : _132349 -> real) : (term15 _132349 f) = (term16 _132349 f).
Proof. exact (fun_ext (fun g : _132349 -> real => @lem7081210 _132349 f g)). Qed.
Lemma lem7081216 {_132349 : Type'} : (@all (_132349 -> real)) = (@all (_132349 -> real)).
Proof. exact (eq_refl (@all (_132349 -> real))). Qed.
Lemma lem7081217 {_132349 : Type'} (f : _132349 -> real) : (term17 _132349 f) = (term18 _132349 f).
Proof. exact (MK_COMB (@lem7081216 _132349) (@lem7081215 _132349 f)). Qed.
Lemma lem7081222 {_132349 : Type'} : (term19 _132349) = (term20 _132349).
Proof. exact (fun_ext (fun f : _132349 -> real => @lem7081217 _132349 f)). Qed.
Lemma lem7081223 {_132349 : Type'} : (@all (_132349 -> real)) = (@all (_132349 -> real)).
Proof. exact (eq_refl (@all (_132349 -> real))). Qed.
Lemma lem7081224 {_132349 : Type'} : (term21 _132349) = (term22 _132349).
Proof. exact (MK_COMB (@lem7081223 _132349) (@lem7081222 _132349)). Qed.
Lemma lem7081229 {_132349 : Type'} : (term22 _132349) = (term21 _132349).
Proof. exact (SYM (@lem7081224 _132349)). Qed.
Lemma lem7081231 {A B : Type'} (op : type1400 B) : term2 A B op.
Proof. exact (EQ_MP (@lem7081159 A B op) (@lem7081158 A B op)). Qed.
Lemma lem7081232 {_132349 : Type'} (op : type1627) : term23 _132349 op.
Proof. exact (@lem7081231 _132349 real op). Qed.
Lemma lem7081233 {_132349 : Type'} : term24 _132349.
Proof. exact (@lem7081232 _132349 real_add). Qed.
Lemma lem7081235 : (@monoidal real real_add) = True.
Proof. exact (EQ_MP (@lem7081143) (@lem7067132)). Qed.
Lemma lem7081236 : True = (@monoidal real real_add).
Proof. exact (SYM (@lem7081235)). Qed.
Lemma lem7081237 : @monoidal real real_add.
Proof. exact (EQ_MP (@lem7081236) (@lem0)). Qed.
Lemma lem7081238 {_132349 : Type'} : term22 _132349.
Proof. exact (@lem7081233 _132349 (@lem7081237)). Qed.
Lemma lem7081239 {_132349 : Type'} : term21 _132349.
Proof. exact (EQ_MP (@lem7081229 _132349) (@lem7081238 _132349)). Qed.
