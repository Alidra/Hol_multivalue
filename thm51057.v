Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm51057_term_abbrevs.
Require Import FORALL_PAIR_THM_spec.
Require Import FUN_EQ_THM_spec.
Lemma lem51007 {A B : Type'} (f : A -> B) : term0 A B f.
Proof. exact (@lem9220 A B f). Qed.
Lemma lem51008 {A B : Type'} (f : A -> B) : (term0 A B f) = (term1 A B f).
Proof. exact (eq_refl (term0 A B f)). Qed.
Lemma lem51009 {A B : Type'} (f : A -> B) : term1 A B f.
Proof. exact (EQ_MP (@lem51008 A B f) (@lem51007 A B f)). Qed.
Lemma lem51010 {A B : Type'} (f : A -> B) (g : A -> B) : term2 A B f g.
Proof. exact (@lem51009 A B f g). Qed.
Lemma lem51011 {A B : Type'} (f : A -> B) (g : A -> B) : (term2 A B f g) = ((f = g) = (term3 A B f g)).
Proof. exact (eq_refl (term2 A B f g)). Qed.
Lemma lem51013 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : term4 _5106 _5107 P.
Proof. exact (@lem49909 _5106 _5107 P). Qed.
Lemma lem51014 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term4 _5106 _5107 P) = ((term5 _5106 _5107 P) = (term6 _5106 _5107 P)).
Proof. exact (eq_refl (term4 _5106 _5107 P)). Qed.
Lemma lem51025 {A B : Type'} (f : A -> B) (g : A -> B) : (f = g) = (term3 A B f g).
Proof. exact (EQ_MP (@lem51011 A B f g) (@lem51010 A B f g)). Qed.
Lemma lem51026 {_5146 _5153 _5154 : Type'} (f : type1228 _5146 _5153 _5154) (g : type1228 _5146 _5153 _5154) : (f = g) = (term7 _5146 _5153 _5154 f g).
Proof. exact (@lem51025 (prod _5154 _5153) _5146 f g). Qed.
Lemma lem51027 {_5146 _5153 _5154 : Type'} (t : type1228 _5146 _5153 _5154) : ((term8 _5146 _5153 _5154 t) = (term9 _5146 _5153 _5154 t)) = (term10 _5146 _5153 _5154 t).
Proof. exact (@lem51026 _5146 _5153 _5154 (term8 _5146 _5153 _5154 t) (term9 _5146 _5153 _5154 t)). Qed.
Lemma lem51033 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term5 _5106 _5107 P) = (term6 _5106 _5107 P).
Proof. exact (EQ_MP (@lem51014 _5106 _5107 P) (@lem51013 _5106 _5107 P)). Qed.
Lemma lem51034 {_5153 _5154 : Type'} (P : type1223 _5153 _5154) : (term5 _5153 _5154 P) = (term6 _5153 _5154 P).
Proof. exact (@lem51033 _5153 _5154 P). Qed.
Lemma lem51035 {_5146 _5153 _5154 : Type'} (t : type1228 _5146 _5153 _5154) : (term11 _5146 _5153 _5154 t) = (term12 _5146 _5153 _5154 t).
Proof. exact (@lem51034 _5153 _5154 (term13 _5146 _5153 _5154 t)). Qed.
Lemma lem51036 {_5146 _5153 _5154 : Type'} (t : type1228 _5146 _5153 _5154) (x : prod _5154 _5153) : (term14 _5146 _5153 _5154 t x) = ((term15 _5146 _5153 _5154 t x) = (term16 _5146 _5153 _5154 t x)).
Proof. exact (eq_refl (term14 _5146 _5153 _5154 t x)). Qed.
Lemma lem51037 {_5146 _5153 _5154 : Type'} (t : type1228 _5146 _5153 _5154) : (term17 _5146 _5153 _5154 t) = (term13 _5146 _5153 _5154 t).
Proof. exact (fun_ext (fun x : prod _5154 _5153 => @lem51036 _5146 _5153 _5154 t x)). Qed.
Lemma lem51038 {_5153 _5154 : Type'} : (@all (prod _5154 _5153)) = (@all (prod _5154 _5153)).
Proof. exact (eq_refl (@all (prod _5154 _5153))). Qed.
Lemma lem51039 {_5146 _5153 _5154 : Type'} (t : type1228 _5146 _5153 _5154) : (term11 _5146 _5153 _5154 t) = (term10 _5146 _5153 _5154 t).
Proof. exact (MK_COMB (@lem51038 _5153 _5154) (@lem51037 _5146 _5153 _5154 t)). Qed.
Lemma lem51040 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem51041 {_5146 _5153 _5154 : Type'} (t : type1228 _5146 _5153 _5154) : (term18 _5146 _5153 _5154 t) = (term19 _5146 _5153 _5154 t).
Proof. exact (MK_COMB (@lem51040) (@lem51039 _5146 _5153 _5154 t)). Qed.
Lemma lem51042 {_5146 _5153 _5154 : Type'} (t : type1228 _5146 _5153 _5154) (p1 : _5154) (p2 : _5153) : (term20 _5146 _5153 _5154 t p1 p2) = ((term21 _5146 _5153 _5154 t p1 p2) = (term22 _5146 _5153 _5154 t p1 p2)).
Proof. exact (eq_refl (term20 _5146 _5153 _5154 t p1 p2)). Qed.
Lemma lem51043 {_5146 _5153 _5154 : Type'} (t : type1228 _5146 _5153 _5154) (p1 : _5154) : (term23 _5146 _5153 _5154 t p1) = (term24 _5146 _5153 _5154 t p1).
Proof. exact (fun_ext (fun p2 : _5153 => @lem51042 _5146 _5153 _5154 t p1 p2)). Qed.
Lemma lem51044 {_5153 : Type'} : (@all _5153) = (@all _5153).
Proof. exact (eq_refl (@all _5153)). Qed.
Lemma lem51045 {_5146 _5153 _5154 : Type'} (t : type1228 _5146 _5153 _5154) (p1 : _5154) : (term25 _5146 _5153 _5154 t p1) = (term26 _5146 _5153 _5154 t p1).
Proof. exact (MK_COMB (@lem51044 _5153) (@lem51043 _5146 _5153 _5154 t p1)). Qed.
Lemma lem51046 {_5146 _5153 _5154 : Type'} (t : type1228 _5146 _5153 _5154) : (term27 _5146 _5153 _5154 t) = (term28 _5146 _5153 _5154 t).
Proof. exact (fun_ext (fun p1 : _5154 => @lem51045 _5146 _5153 _5154 t p1)). Qed.
Lemma lem51047 {_5154 : Type'} : (@all _5154) = (@all _5154).
Proof. exact (eq_refl (@all _5154)). Qed.
Lemma lem51048 {_5146 _5153 _5154 : Type'} (t : type1228 _5146 _5153 _5154) : (term12 _5146 _5153 _5154 t) = (term29 _5146 _5153 _5154 t).
Proof. exact (MK_COMB (@lem51047 _5154) (@lem51046 _5146 _5153 _5154 t)). Qed.
Lemma lem51049 {_5146 _5153 _5154 : Type'} (t : type1228 _5146 _5153 _5154) : ((term11 _5146 _5153 _5154 t) = (term12 _5146 _5153 _5154 t)) = ((term10 _5146 _5153 _5154 t) = (term29 _5146 _5153 _5154 t)).
Proof. exact (MK_COMB (@lem51041 _5146 _5153 _5154 t) (@lem51048 _5146 _5153 _5154 t)). Qed.
Lemma lem51050 {_5146 _5153 _5154 : Type'} (t : type1228 _5146 _5153 _5154) : (term10 _5146 _5153 _5154 t) = (term29 _5146 _5153 _5154 t).
Proof. exact (EQ_MP (@lem51049 _5146 _5153 _5154 t) (@lem51035 _5146 _5153 _5154 t)). Qed.
Lemma lem51057 {_5146 _5153 _5154 : Type'} (t : type1228 _5146 _5153 _5154) : ((term8 _5146 _5153 _5154 t) = (term9 _5146 _5153 _5154 t)) = (term29 _5146 _5153 _5154 t).
Proof. exact (TRANS (@lem51027 _5146 _5153 _5154 t) (@lem51050 _5146 _5153 _5154 t)). Qed.
