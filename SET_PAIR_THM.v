Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SET_PAIR_THM_term_abbrevs.
Require Import EXTENSION_spec.
Require Import FORALL_PAIR_THM_spec.
Require Import IN_ELIM_PAIR_THM_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm3184736_spec.
Require Import thm3184739_spec.
Lemma lem3421068 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) : term0 _88435 _88436 P.
Proof. exact (@lem3405756 _88435 _88436 P). Qed.
Lemma lem3421069 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) : (term0 _88435 _88436 P) = (term1 _88435 _88436 P).
Proof. exact (eq_refl (term0 _88435 _88436 P)). Qed.
Lemma lem3421070 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) : term1 _88435 _88436 P.
Proof. exact (EQ_MP (@lem3421069 _88435 _88436 P) (@lem3421068 _88435 _88436 P)). Qed.
Lemma lem3421071 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) : term2 _88435 _88436 P a.
Proof. exact (@lem3421070 _88435 _88436 P a). Qed.
Lemma lem3421072 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) : (term2 _88435 _88436 P a) = (term3 _88435 _88436 P a).
Proof. exact (eq_refl (term2 _88435 _88436 P a)). Qed.
Lemma lem3421073 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) : term3 _88435 _88436 P a.
Proof. exact (EQ_MP (@lem3421072 _88435 _88436 P a) (@lem3421071 _88435 _88436 P a)). Qed.
Lemma lem3421074 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) : term4 _88435 _88436 P a b.
Proof. exact (@lem3421073 _88435 _88436 P a b). Qed.
Lemma lem3421075 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) : (term4 _88435 _88436 P a b) = ((term5 _88435 _88436 a b P) = (P a b)).
Proof. exact (eq_refl (term4 _88435 _88436 P a b)). Qed.
Lemma lem3421101 {_83095 : Type'} : term6 _83095.
Proof. exact (EQ_MP (@lem3184739 _83095) (@lem3184736 _83095)). Qed.
Lemma lem3421102 {_83095 : Type'} (p : _83095 -> Prop) : term7 _83095 p.
Proof. exact (@lem3421101 _83095 p). Qed.
Lemma lem3421103 {_83095 : Type'} (p : _83095 -> Prop) : (term7 _83095 p) = (term8 _83095 p).
Proof. exact (eq_refl (term7 _83095 p)). Qed.
Lemma lem3421104 {_83095 : Type'} (p : _83095 -> Prop) : term8 _83095 p.
Proof. exact (EQ_MP (@lem3421103 _83095 p) (@lem3421102 _83095 p)). Qed.
Lemma lem3421105 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : term9 _83095 p x.
Proof. exact (@lem3421104 _83095 p x). Qed.
Lemma lem3421106 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term9 _83095 p x) = ((term10 _83095 x p) = (p x)).
Proof. exact (eq_refl (term9 _83095 p x)). Qed.
Lemma lem3421115 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : term11 _5106 _5107 P.
Proof. exact (@lem49909 _5106 _5107 P). Qed.
Lemma lem3421116 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term11 _5106 _5107 P) = ((term12 _5106 _5107 P) = (term13 _5106 _5107 P)).
Proof. exact (eq_refl (term11 _5106 _5107 P)). Qed.
Lemma lem3421118 {A : Type'} (s : A -> Prop) : term14 A s.
Proof. exact (@lem3181245 A s). Qed.
Lemma lem3421119 {A : Type'} (s : A -> Prop) : (term14 A s) = (term15 A s).
Proof. exact (eq_refl (term14 A s)). Qed.
Lemma lem3421120 {A : Type'} (s : A -> Prop) : term15 A s.
Proof. exact (EQ_MP (@lem3421119 A s) (@lem3421118 A s)). Qed.
Lemma lem3421121 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term16 A s t.
Proof. exact (@lem3421120 A s t). Qed.
Lemma lem3421122 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term16 A s t) = ((s = t) = (term17 A s t)).
Proof. exact (eq_refl (term16 A s t)). Qed.
Lemma lem3421133 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term17 A s t).
Proof. exact (EQ_MP (@lem3421122 A s t) (@lem3421121 A s t)). Qed.
Lemma lem3421134 {_88856 _88857 : Type'} (s : type1223 _88856 _88857) (t : type1223 _88856 _88857) : (s = t) = (term18 _88856 _88857 s t).
Proof. exact (@lem3421133 (prod _88857 _88856) s t). Qed.
Lemma lem3421135 {_88856 _88857 : Type'} (P : type1223 _88856 _88857) : ((term19 _88856 _88857 P) = (term20 _88856 _88857 P)) = (term21 _88856 _88857 P).
Proof. exact (@lem3421134 _88856 _88857 (term19 _88856 _88857 P) (term20 _88856 _88857 P)). Qed.
Lemma lem3421141 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term12 _5106 _5107 P) = (term13 _5106 _5107 P).
Proof. exact (EQ_MP (@lem3421116 _5106 _5107 P) (@lem3421115 _5106 _5107 P)). Qed.
Lemma lem3421142 {_88856 _88857 : Type'} (P : type1223 _88856 _88857) : (term12 _88856 _88857 P) = (term13 _88856 _88857 P).
Proof. exact (@lem3421141 _88856 _88857 P). Qed.
Lemma lem3421143 {_88856 _88857 : Type'} (P : type1223 _88856 _88857) : (term22 _88856 _88857 P) = (term23 _88856 _88857 P).
Proof. exact (@lem3421142 _88856 _88857 (term24 _88856 _88857 P)). Qed.
Lemma lem3421144 {_88856 _88857 : Type'} (x : prod _88857 _88856) (P : type1223 _88856 _88857) : (term25 _88856 _88857 P x) = ((term26 _88856 _88857 x P) = (term27 _88856 _88857 x P)).
Proof. exact (eq_refl (term25 _88856 _88857 P x)). Qed.
Lemma lem3421145 {_88856 _88857 : Type'} (P : type1223 _88856 _88857) : (term28 _88856 _88857 P) = (term24 _88856 _88857 P).
Proof. exact (fun_ext (fun x : prod _88857 _88856 => @lem3421144 _88856 _88857 x P)). Qed.
Lemma lem3421146 {_88856 _88857 : Type'} : (@all (prod _88857 _88856)) = (@all (prod _88857 _88856)).
Proof. exact (eq_refl (@all (prod _88857 _88856))). Qed.
Lemma lem3421147 {_88856 _88857 : Type'} (P : type1223 _88856 _88857) : (term22 _88856 _88857 P) = (term21 _88856 _88857 P).
Proof. exact (MK_COMB (@lem3421146 _88856 _88857) (@lem3421145 _88856 _88857 P)). Qed.
Lemma lem3421148 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3421149 {_88856 _88857 : Type'} (P : type1223 _88856 _88857) : (term29 _88856 _88857 P) = (term30 _88856 _88857 P).
Proof. exact (MK_COMB (@lem3421148) (@lem3421147 _88856 _88857 P)). Qed.
Lemma lem3421150 {_88856 _88857 : Type'} (p1 : _88857) (p2 : _88856) (P : type1223 _88856 _88857) : (term31 _88856 _88857 P p1 p2) = ((term32 _88856 _88857 p1 p2 P) = (term33 _88856 _88857 p1 p2 P)).
Proof. exact (eq_refl (term31 _88856 _88857 P p1 p2)). Qed.
Lemma lem3421151 {_88856 _88857 : Type'} (p1 : _88857) (P : type1223 _88856 _88857) : (term34 _88856 _88857 P p1) = (term35 _88856 _88857 p1 P).
Proof. exact (fun_ext (fun p2 : _88856 => @lem3421150 _88856 _88857 p1 p2 P)). Qed.
Lemma lem3421152 {_88856 : Type'} : (@all _88856) = (@all _88856).
Proof. exact (eq_refl (@all _88856)). Qed.
Lemma lem3421153 {_88856 _88857 : Type'} (p1 : _88857) (P : type1223 _88856 _88857) : (term36 _88856 _88857 P p1) = (term37 _88856 _88857 p1 P).
Proof. exact (MK_COMB (@lem3421152 _88856) (@lem3421151 _88856 _88857 p1 P)). Qed.
Lemma lem3421154 {_88856 _88857 : Type'} (P : type1223 _88856 _88857) : (term38 _88856 _88857 P) = (term39 _88856 _88857 P).
Proof. exact (fun_ext (fun p1 : _88857 => @lem3421153 _88856 _88857 p1 P)). Qed.
Lemma lem3421155 {_88857 : Type'} : (@all _88857) = (@all _88857).
Proof. exact (eq_refl (@all _88857)). Qed.
Lemma lem3421156 {_88856 _88857 : Type'} (P : type1223 _88856 _88857) : (term23 _88856 _88857 P) = (term40 _88856 _88857 P).
Proof. exact (MK_COMB (@lem3421155 _88857) (@lem3421154 _88856 _88857 P)). Qed.
Lemma lem3421157 {_88856 _88857 : Type'} (P : type1223 _88856 _88857) : ((term22 _88856 _88857 P) = (term23 _88856 _88857 P)) = ((term21 _88856 _88857 P) = (term40 _88856 _88857 P)).
Proof. exact (MK_COMB (@lem3421149 _88856 _88857 P) (@lem3421156 _88856 _88857 P)). Qed.
Lemma lem3421158 {_88856 _88857 : Type'} (P : type1223 _88856 _88857) : (term21 _88856 _88857 P) = (term40 _88856 _88857 P).
Proof. exact (EQ_MP (@lem3421157 _88856 _88857 P) (@lem3421143 _88856 _88857 P)). Qed.
Lemma lem3421165 {_88856 _88857 : Type'} (P : type1223 _88856 _88857) : ((term19 _88856 _88857 P) = (term20 _88856 _88857 P)) = (term40 _88856 _88857 P).
Proof. exact (TRANS (@lem3421135 _88856 _88857 P) (@lem3421158 _88856 _88857 P)). Qed.
Lemma lem3421177 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term10 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem3421106 _83095 p x) (@lem3421105 _83095 p x)). Qed.
Lemma lem3421178 {_88856 _88857 : Type'} (p : type1223 _88856 _88857) (x : prod _88857 _88856) : (term26 _88856 _88857 x p) = (p x).
Proof. exact (@lem3421177 (prod _88857 _88856) p x). Qed.
Lemma lem3421179 {_88856 _88857 : Type'} (P : type1223 _88856 _88857) (p1 : _88857) (p2 : _88856) : (term32 _88856 _88857 p1 p2 P) = (term41 _88856 _88857 P p1 p2).
Proof. exact (@lem3421178 _88856 _88857 P (@pair _88857 _88856 p1 p2)). Qed.
Lemma lem3421180 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3421181 {_88856 _88857 : Type'} (P : type1223 _88856 _88857) (p1 : _88857) (p2 : _88856) : (term42 _88856 _88857 p1 p2 P) = (term43 _88856 _88857 P p1 p2).
Proof. exact (MK_COMB (@lem3421180) (@lem3421179 _88856 _88857 P p1 p2)). Qed.
Lemma lem3421183 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) : (term5 _88435 _88436 a b P) = (P a b).
Proof. exact (EQ_MP (@lem3421075 _88435 _88436 P a b) (@lem3421074 _88435 _88436 P a b)). Qed.
Lemma lem3421184 {_88856 _88857 : Type'} (P : type1470 _88856 _88857) (a : _88857) (b : _88856) : (term5 _88856 _88857 a b P) = (P a b).
Proof. exact (@lem3421183 _88856 _88857 P a b). Qed.
Lemma lem3421185 {_88856 _88857 : Type'} (P : type1223 _88856 _88857) (p1 : _88857) (p2 : _88856) : (term44 _88856 _88857 p1 p2 P) = (term45 _88856 _88857 P p1 p2).
Proof. exact (@lem3421184 _88856 _88857 (term46 _88856 _88857 P) p1 p2). Qed.
Lemma lem3421186 {_88856 _88857 : Type'} (P : type1223 _88856 _88857) (a : _88857) : (term47 _88856 _88857 P a) = (term48 _88856 _88857 P a).
Proof. exact (eq_refl (term47 _88856 _88857 P a)). Qed.
Lemma lem3421187 {_88856 : Type'} (b : _88856) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem3421188 {_88856 _88857 : Type'} (P : type1223 _88856 _88857) (a : _88857) (b : _88856) : (term45 _88856 _88857 P a b) = (term49 _88856 _88857 P a b).
Proof. exact (MK_COMB (@lem3421186 _88856 _88857 P a) (@lem3421187 _88856 b)). Qed.
Lemma lem3421189 {_88856 _88857 : Type'} (P : type1223 _88856 _88857) (a : _88857) (b : _88856) : (term49 _88856 _88857 P a b) = (term41 _88856 _88857 P a b).
Proof. exact (eq_refl (term49 _88856 _88857 P a b)). Qed.
Lemma lem3421190 {_88856 _88857 : Type'} (P : type1223 _88856 _88857) (a : _88857) (b : _88856) : (term45 _88856 _88857 P a b) = (term41 _88856 _88857 P a b).
Proof. exact (TRANS (@lem3421188 _88856 _88857 P a b) (@lem3421189 _88856 _88857 P a b)). Qed.
Lemma lem3421191 {_88856 _88857 : Type'} (GEN_PVAR_38 : prod _88857 _88856) : (@SETSPEC (prod _88857 _88856) GEN_PVAR_38) = (@SETSPEC (prod _88857 _88856) GEN_PVAR_38).
Proof. exact (eq_refl (@SETSPEC (prod _88857 _88856) GEN_PVAR_38)). Qed.
Lemma lem3421192 {_88856 _88857 : Type'} (GEN_PVAR_38 : prod _88857 _88856) (P : type1223 _88856 _88857) (a : _88857) (b : _88856) : (term50 _88856 _88857 GEN_PVAR_38 P a b) = (term51 _88856 _88857 GEN_PVAR_38 P a b).
Proof. exact (MK_COMB (@lem3421191 _88856 _88857 GEN_PVAR_38) (@lem3421190 _88856 _88857 P a b)). Qed.
Lemma lem3421193 {_88856 _88857 : Type'} (a : _88857) (b : _88856) : (@pair _88857 _88856 a b) = (@pair _88857 _88856 a b).
Proof. exact (eq_refl (@pair _88857 _88856 a b)). Qed.
Lemma lem3421194 {_88856 _88857 : Type'} (GEN_PVAR_38 : prod _88857 _88856) (P : type1223 _88856 _88857) (a : _88857) (b : _88856) : (term52 _88856 _88857 GEN_PVAR_38 P a b) = (term53 _88856 _88857 GEN_PVAR_38 P a b).
Proof. exact (MK_COMB (@lem3421192 _88856 _88857 GEN_PVAR_38 P a b) (@lem3421193 _88856 _88857 a b)). Qed.
Lemma lem3421195 {_88856 _88857 : Type'} (GEN_PVAR_38 : prod _88857 _88856) (P : type1223 _88856 _88857) (a : _88857) : (term54 _88856 _88857 GEN_PVAR_38 P a) = (term55 _88856 _88857 GEN_PVAR_38 P a).
Proof. exact (fun_ext (fun b : _88856 => @lem3421194 _88856 _88857 GEN_PVAR_38 P a b)). Qed.
Lemma lem3421196 {_88856 : Type'} : (@ex _88856) = (@ex _88856).
Proof. exact (eq_refl (@ex _88856)). Qed.
Lemma lem3421197 {_88856 _88857 : Type'} (GEN_PVAR_38 : prod _88857 _88856) (P : type1223 _88856 _88857) (a : _88857) : (term56 _88856 _88857 GEN_PVAR_38 P a) = (term57 _88856 _88857 GEN_PVAR_38 P a).
Proof. exact (MK_COMB (@lem3421196 _88856) (@lem3421195 _88856 _88857 GEN_PVAR_38 P a)). Qed.
Lemma lem3421198 {_88856 _88857 : Type'} (GEN_PVAR_38 : prod _88857 _88856) (P : type1223 _88856 _88857) : (term58 _88856 _88857 GEN_PVAR_38 P) = (term59 _88856 _88857 GEN_PVAR_38 P).
Proof. exact (fun_ext (fun a : _88857 => @lem3421197 _88856 _88857 GEN_PVAR_38 P a)). Qed.
Lemma lem3421199 {_88857 : Type'} : (@ex _88857) = (@ex _88857).
Proof. exact (eq_refl (@ex _88857)). Qed.
Lemma lem3421200 {_88856 _88857 : Type'} (GEN_PVAR_38 : prod _88857 _88856) (P : type1223 _88856 _88857) : (term60 _88856 _88857 GEN_PVAR_38 P) = (term61 _88856 _88857 GEN_PVAR_38 P).
Proof. exact (MK_COMB (@lem3421199 _88857) (@lem3421198 _88856 _88857 GEN_PVAR_38 P)). Qed.
Lemma lem3421201 {_88856 _88857 : Type'} (P : type1223 _88856 _88857) : (term62 _88856 _88857 P) = (term63 _88856 _88857 P).
Proof. exact (fun_ext (fun GEN_PVAR_38 : prod _88857 _88856 => @lem3421200 _88856 _88857 GEN_PVAR_38 P)). Qed.
Lemma lem3421202 {_88856 _88857 : Type'} : (@GSPEC (prod _88857 _88856)) = (@GSPEC (prod _88857 _88856)).
Proof. exact (eq_refl (@GSPEC (prod _88857 _88856))). Qed.
Lemma lem3421203 {_88856 _88857 : Type'} (P : type1223 _88856 _88857) : (term64 _88856 _88857 P) = (term20 _88856 _88857 P).
Proof. exact (MK_COMB (@lem3421202 _88856 _88857) (@lem3421201 _88856 _88857 P)). Qed.
Lemma lem3421204 {_88856 _88857 : Type'} (p1 : _88857) (p2 : _88856) : (term65 _88856 _88857 p1 p2) = (term65 _88856 _88857 p1 p2).
Proof. exact (eq_refl (term65 _88856 _88857 p1 p2)). Qed.
Lemma lem3421205 {_88856 _88857 : Type'} (p1 : _88857) (p2 : _88856) (P : type1223 _88856 _88857) : (term44 _88856 _88857 p1 p2 P) = (term33 _88856 _88857 p1 p2 P).
Proof. exact (MK_COMB (@lem3421204 _88856 _88857 p1 p2) (@lem3421203 _88856 _88857 P)). Qed.
Lemma lem3421206 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3421207 {_88856 _88857 : Type'} (p1 : _88857) (p2 : _88856) (P : type1223 _88856 _88857) : (term66 _88856 _88857 p1 p2 P) = (term67 _88856 _88857 p1 p2 P).
Proof. exact (MK_COMB (@lem3421206) (@lem3421205 _88856 _88857 p1 p2 P)). Qed.
Lemma lem3421208 {_88856 _88857 : Type'} (P : type1223 _88856 _88857) (p1 : _88857) : (term47 _88856 _88857 P p1) = (term48 _88856 _88857 P p1).
Proof. exact (eq_refl (term47 _88856 _88857 P p1)). Qed.
Lemma lem3421209 {_88856 : Type'} (p2 : _88856) : p2 = p2.
Proof. exact (eq_refl p2). Qed.
Lemma lem3421210 {_88856 _88857 : Type'} (P : type1223 _88856 _88857) (p1 : _88857) (p2 : _88856) : (term45 _88856 _88857 P p1 p2) = (term49 _88856 _88857 P p1 p2).
Proof. exact (MK_COMB (@lem3421208 _88856 _88857 P p1) (@lem3421209 _88856 p2)). Qed.
Lemma lem3421211 {_88856 _88857 : Type'} (P : type1223 _88856 _88857) (p1 : _88857) (p2 : _88856) : (term49 _88856 _88857 P p1 p2) = (term41 _88856 _88857 P p1 p2).
Proof. exact (eq_refl (term49 _88856 _88857 P p1 p2)). Qed.
Lemma lem3421212 {_88856 _88857 : Type'} (P : type1223 _88856 _88857) (p1 : _88857) (p2 : _88856) : (term45 _88856 _88857 P p1 p2) = (term41 _88856 _88857 P p1 p2).
Proof. exact (TRANS (@lem3421210 _88856 _88857 P p1 p2) (@lem3421211 _88856 _88857 P p1 p2)). Qed.
Lemma lem3421213 {_88856 _88857 : Type'} (P : type1223 _88856 _88857) (p1 : _88857) (p2 : _88856) : ((term44 _88856 _88857 p1 p2 P) = (term45 _88856 _88857 P p1 p2)) = ((term33 _88856 _88857 p1 p2 P) = (term41 _88856 _88857 P p1 p2)).
Proof. exact (MK_COMB (@lem3421207 _88856 _88857 p1 p2 P) (@lem3421212 _88856 _88857 P p1 p2)). Qed.
Lemma lem3421214 {_88856 _88857 : Type'} (P : type1223 _88856 _88857) (p1 : _88857) (p2 : _88856) : (term33 _88856 _88857 p1 p2 P) = (term41 _88856 _88857 P p1 p2).
Proof. exact (EQ_MP (@lem3421213 _88856 _88857 P p1 p2) (@lem3421185 _88856 _88857 P p1 p2)). Qed.
Lemma lem3421215 {_88856 _88857 : Type'} (P : type1223 _88856 _88857) (p1 : _88857) (p2 : _88856) : ((term32 _88856 _88857 p1 p2 P) = (term33 _88856 _88857 p1 p2 P)) = ((term41 _88856 _88857 P p1 p2) = (term41 _88856 _88857 P p1 p2)).
Proof. exact (MK_COMB (@lem3421181 _88856 _88857 P p1 p2) (@lem3421214 _88856 _88857 P p1 p2)). Qed.
Lemma lem3421217 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3421218 (x : Prop) : (x = x) = True.
Proof. exact (@lem3421217 Prop x). Qed.
Lemma lem3421219 {_88856 _88857 : Type'} (P : type1223 _88856 _88857) (p1 : _88857) (p2 : _88856) : ((term41 _88856 _88857 P p1 p2) = (term41 _88856 _88857 P p1 p2)) = True.
Proof. exact (@lem3421218 (term41 _88856 _88857 P p1 p2)). Qed.
Lemma lem3421220 {_88856 _88857 : Type'} (p1 : _88857) (p2 : _88856) (P : type1223 _88856 _88857) : ((term32 _88856 _88857 p1 p2 P) = (term33 _88856 _88857 p1 p2 P)) = True.
Proof. exact (TRANS (@lem3421215 _88856 _88857 P p1 p2) (@lem3421219 _88856 _88857 P p1 p2)). Qed.
Lemma lem3421221 {_88856 _88857 : Type'} (p1 : _88857) (P : type1223 _88856 _88857) : (term35 _88856 _88857 p1 P) = (term68 _88856).
Proof. exact (fun_ext (fun p2 : _88856 => @lem3421220 _88856 _88857 p1 p2 P)). Qed.
Lemma lem3421222 {_88856 : Type'} : (@all _88856) = (@all _88856).
Proof. exact (eq_refl (@all _88856)). Qed.
Lemma lem3421223 {_88856 _88857 : Type'} (p1 : _88857) (P : type1223 _88856 _88857) : (term37 _88856 _88857 p1 P) = (term69 _88856).
Proof. exact (MK_COMB (@lem3421222 _88856) (@lem3421221 _88856 _88857 p1 P)). Qed.
Lemma lem3421225 {A : Type'} (t : Prop) : (term70 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3421226 {_88856 : Type'} (t : Prop) : (term70 _88856 t) = t.
Proof. exact (@lem3421225 _88856 t). Qed.
Lemma lem3421227 {_88856 : Type'} : (term69 _88856) = True.
Proof. exact (@lem3421226 _88856 True). Qed.
Lemma lem3421228 {_88856 _88857 : Type'} (p1 : _88857) (P : type1223 _88856 _88857) : (term37 _88856 _88857 p1 P) = True.
Proof. exact (TRANS (@lem3421223 _88856 _88857 p1 P) (@lem3421227 _88856)). Qed.
Lemma lem3421229 {_88856 _88857 : Type'} (P : type1223 _88856 _88857) : (term39 _88856 _88857 P) = (term68 _88857).
Proof. exact (fun_ext (fun p1 : _88857 => @lem3421228 _88856 _88857 p1 P)). Qed.
Lemma lem3421230 {_88857 : Type'} : (@all _88857) = (@all _88857).
Proof. exact (eq_refl (@all _88857)). Qed.
Lemma lem3421231 {_88856 _88857 : Type'} (P : type1223 _88856 _88857) : (term40 _88856 _88857 P) = (term69 _88857).
Proof. exact (MK_COMB (@lem3421230 _88857) (@lem3421229 _88856 _88857 P)). Qed.
Lemma lem3421233 {A : Type'} (t : Prop) : (term70 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3421234 {_88857 : Type'} (t : Prop) : (term70 _88857 t) = t.
Proof. exact (@lem3421233 _88857 t). Qed.
Lemma lem3421235 {_88857 : Type'} : (term69 _88857) = True.
Proof. exact (@lem3421234 _88857 True). Qed.
Lemma lem3421236 {_88856 _88857 : Type'} (P : type1223 _88856 _88857) : (term40 _88856 _88857 P) = True.
Proof. exact (TRANS (@lem3421231 _88856 _88857 P) (@lem3421235 _88857)). Qed.
Lemma lem3421237 {_88856 _88857 : Type'} (P : type1223 _88856 _88857) : ((term19 _88856 _88857 P) = (term20 _88856 _88857 P)) = True.
Proof. exact (TRANS (@lem3421165 _88856 _88857 P) (@lem3421236 _88856 _88857 P)). Qed.
Lemma lem3421238 {_88856 _88857 : Type'} : (term71 _88856 _88857) = (term72 _88856 _88857).
Proof. exact (fun_ext (fun P : type1223 _88856 _88857 => @lem3421237 _88856 _88857 P)). Qed.
Lemma lem3421239 {_88856 _88857 : Type'} : (@all ((prod _88857 _88856) -> Prop)) = (@all ((prod _88857 _88856) -> Prop)).
Proof. exact (eq_refl (@all ((prod _88857 _88856) -> Prop))). Qed.
Lemma lem3421240 {_88856 _88857 : Type'} : (term73 _88856 _88857) = (term74 _88856 _88857).
Proof. exact (MK_COMB (@lem3421239 _88856 _88857) (@lem3421238 _88856 _88857)). Qed.
Lemma lem3421242 {A : Type'} (t : Prop) : (term70 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3421243 {_88856 _88857 : Type'} (t : Prop) : (term75 _88856 _88857 t) = t.
Proof. exact (@lem3421242 (type1223 _88856 _88857) t). Qed.
Lemma lem3421244 {_88856 _88857 : Type'} : (term74 _88856 _88857) = True.
Proof. exact (@lem3421243 _88856 _88857 True). Qed.
Lemma lem3421245 {_88856 _88857 : Type'} : (term73 _88856 _88857) = True.
Proof. exact (TRANS (@lem3421240 _88856 _88857) (@lem3421244 _88856 _88857)). Qed.
Lemma lem3421246 {_88856 _88857 : Type'} : True = (term73 _88856 _88857).
Proof. exact (SYM (@lem3421245 _88856 _88857)). Qed.
Lemma lem3421247 {_88856 _88857 : Type'} : term73 _88856 _88857.
Proof. exact (EQ_MP (@lem3421246 _88856 _88857) (@lem0)). Qed.
