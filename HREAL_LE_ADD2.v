Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import HREAL_LE_ADD2_term_abbrevs.
Require Import HREAL_ADD_AC_spec.
Require Import HREAL_LE_EXISTS_DEF_spec.
Require Import thm0_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem1322004 (m : hreal) : term0 m.
Proof. exact (@lem1321284 m). Qed.
Lemma lem1322005 (m : hreal) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem1322006 (m : hreal) : term1 m.
Proof. exact (EQ_MP (@lem1322005 m) (@lem1322004 m)). Qed.
Lemma lem1322007 (m : hreal) (n : hreal) : term2 m n.
Proof. exact (@lem1322006 m n). Qed.
Lemma lem1322008 (n : hreal) (m : hreal) : (term2 m n) = ((hreal_le m n) = (term3 n m)).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem1322015 (n : hreal) (m : hreal) : (hreal_le m n) = (term3 n m).
Proof. exact (EQ_MP (@lem1322008 n m) (@lem1322007 m n)). Qed.
Lemma lem1322016 (b : hreal) (a : hreal) : (hreal_le a b) = (term3 b a).
Proof. exact (@lem1322015 b a). Qed.
Lemma lem1322023 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1322024 (b : hreal) (a : hreal) : (term4 a b) = (term5 b a).
Proof. exact (MK_COMB (@lem1322023) (@lem1322016 b a)). Qed.
Lemma lem1322026 (n : hreal) (m : hreal) : (hreal_le m n) = (term3 n m).
Proof. exact (EQ_MP (@lem1322008 n m) (@lem1322007 m n)). Qed.
Lemma lem1322027 (d : hreal) (c : hreal) : (hreal_le c d) = (term3 d c).
Proof. exact (@lem1322026 d c). Qed.
Lemma lem1322034 (b : hreal) (a : hreal) (d : hreal) (c : hreal) : (term6 a b c d) = (term7 b a d c).
Proof. exact (MK_COMB (@lem1322024 b a) (@lem1322027 d c)). Qed.
Lemma lem1322037 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1322038 (b : hreal) (a : hreal) (d : hreal) (c : hreal) : (term8 a b c d) = (term9 b a d c).
Proof. exact (MK_COMB (@lem1322037) (@lem1322034 b a d c)). Qed.
Lemma lem1322040 (n : hreal) (m : hreal) : (hreal_le m n) = (term3 n m).
Proof. exact (EQ_MP (@lem1322008 n m) (@lem1322007 m n)). Qed.
Lemma lem1322041 (b : hreal) (d : hreal) (a : hreal) (c : hreal) : (term10 a c b d) = (term11 b d a c).
Proof. exact (@lem1322040 (hreal_add b d) (hreal_add a c)). Qed.
Lemma lem1322048 (b : hreal) (d : hreal) (a : hreal) (c : hreal) : (term12 a c b d) = (term13 b d a c).
Proof. exact (MK_COMB (@lem1322038 b a d c) (@lem1322041 b d a c)). Qed.
Lemma lem1322051 (a : hreal) (c : hreal) (b : hreal) (d : hreal) : (term13 b d a c) = (term12 a c b d).
Proof. exact (SYM (@lem1322048 b d a c)). Qed.
Lemma lem1322052 (b : hreal) (a : hreal) (d : hreal) (c : hreal) (h1 : term7 b a d c) : term7 b a d c.
Proof. exact (h1). Qed.
Lemma lem1322053 (d : hreal) (c : hreal) (h1 : term3 d c) : term3 d c.
Proof. exact (h1). Qed.
Lemma lem1322055 (b : hreal) (a : hreal) (h1 : term3 b a) : term3 b a.
Proof. exact (h1). Qed.
Lemma lem1322057 (n : hreal) (m : hreal) (p : hreal) : term14 n m p.
Proof. exact (proj2 (@lem1322003 n m p)). Qed.
Lemma lem1322067 (b : hreal) (a : hreal) (d1 : hreal) (h1 : b = (hreal_add a d1)) : b = (hreal_add a d1).
Proof. exact (h1). Qed.
Lemma lem1322071 : hreal_add = hreal_add.
Proof. exact (eq_refl hreal_add). Qed.
Lemma lem1322072 (b : hreal) (a : hreal) (d1 : hreal) (h1 : b = (hreal_add a d1)) : (hreal_add b) = (term15 a d1).
Proof. exact (MK_COMB (@lem1322071) (@lem1322067 b a d1 h1)). Qed.
Lemma lem1322074 (d : hreal) (c : hreal) (d2 : hreal) (h1 : d = (hreal_add c d2)) : d = (hreal_add c d2).
Proof. exact (h1). Qed.
Lemma lem1322078 (b : hreal) (a : hreal) (d1 : hreal) (d : hreal) (c : hreal) (d2 : hreal) (h1 : b = (hreal_add a d1)) (h2 : d = (hreal_add c d2)) : (hreal_add b d) = (term16 a d1 c d2).
Proof. exact (MK_COMB (@lem1322072 b a d1 h1) (@lem1322074 d c d2 h2)). Qed.
Lemma lem1322080 (m : hreal) (n : hreal) (p : hreal) : (term17 m n p) = (term18 m n p).
Proof. exact (proj1 (@lem1322057 n m p)). Qed.
Lemma lem1322081 (a : hreal) (d1 : hreal) (c : hreal) (d2 : hreal) : (term16 a d1 c d2) = (term19 a d1 c d2).
Proof. exact (@lem1322080 a d1 (hreal_add c d2)). Qed.
Lemma lem1322089 (n : hreal) (m : hreal) (p : hreal) : (term18 m n p) = (term18 n m p).
Proof. exact (proj2 (@lem1322057 n m p)). Qed.
Lemma lem1322090 (c : hreal) (d1 : hreal) (d2 : hreal) : (term18 d1 c d2) = (term18 c d1 d2).
Proof. exact (@lem1322089 c d1 d2). Qed.
Lemma lem1322100 (a : hreal) : (hreal_add a) = (hreal_add a).
Proof. exact (eq_refl (hreal_add a)). Qed.
Lemma lem1322101 (a : hreal) (c : hreal) (d1 : hreal) (d2 : hreal) : (term19 a d1 c d2) = (term19 a c d1 d2).
Proof. exact (MK_COMB (@lem1322100 a) (@lem1322090 c d1 d2)). Qed.
Lemma lem1322108 (a : hreal) (c : hreal) (d1 : hreal) (d2 : hreal) : (term16 a d1 c d2) = (term19 a c d1 d2).
Proof. exact (TRANS (@lem1322081 a d1 c d2) (@lem1322101 a c d1 d2)). Qed.
Lemma lem1322109 (b : hreal) (a : hreal) (d1 : hreal) (d : hreal) (c : hreal) (d2 : hreal) (h1 : b = (hreal_add a d1)) (h2 : d = (hreal_add c d2)) : (hreal_add b d) = (term19 a c d1 d2).
Proof. exact (TRANS (@lem1322078 b a d1 d c d2 h1 h2) (@lem1322108 a c d1 d2)). Qed.
Lemma lem1322110 : (@eq hreal) = (@eq hreal).
Proof. exact (eq_refl (@eq hreal)). Qed.
Lemma lem1322111 (b : hreal) (a : hreal) (d1 : hreal) (d : hreal) (c : hreal) (d2 : hreal) (h1 : b = (hreal_add a d1)) (h2 : d = (hreal_add c d2)) : (term20 b d) = (term21 a c d1 d2).
Proof. exact (MK_COMB (@lem1322110) (@lem1322109 b a d1 d c d2 h1 h2)). Qed.
Lemma lem1322113 (m : hreal) (n : hreal) (p : hreal) : (term17 m n p) = (term18 m n p).
Proof. exact (proj1 (@lem1322057 n m p)). Qed.
Lemma lem1322114 (a : hreal) (c : hreal) (d1 : hreal) (d2 : hreal) : (term16 a c d1 d2) = (term19 a c d1 d2).
Proof. exact (@lem1322113 a c (hreal_add d1 d2)). Qed.
Lemma lem1322130 (b : hreal) (a : hreal) (d1 : hreal) (d : hreal) (c : hreal) (d2 : hreal) (h1 : b = (hreal_add a d1)) (h2 : d = (hreal_add c d2)) : ((hreal_add b d) = (term16 a c d1 d2)) = ((term19 a c d1 d2) = (term19 a c d1 d2)).
Proof. exact (MK_COMB (@lem1322111 b a d1 d c d2 h1 h2) (@lem1322114 a c d1 d2)). Qed.
Lemma lem1322132 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1322133 (x : hreal) : (x = x) = True.
Proof. exact (@lem1322132 hreal x). Qed.
Lemma lem1322134 (a : hreal) (c : hreal) (d1 : hreal) (d2 : hreal) : ((term19 a c d1 d2) = (term19 a c d1 d2)) = True.
Proof. exact (@lem1322133 (term19 a c d1 d2)). Qed.
Lemma lem1322135 (b : hreal) (a : hreal) (d1 : hreal) (d : hreal) (c : hreal) (d2 : hreal) (h1 : b = (hreal_add a d1)) (h2 : d = (hreal_add c d2)) : ((hreal_add b d) = (term16 a c d1 d2)) = True.
Proof. exact (TRANS (@lem1322130 b a d1 d c d2 h1 h2) (@lem1322134 a c d1 d2)). Qed.
Lemma lem1322136 (b : hreal) (a : hreal) (d1 : hreal) (d : hreal) (c : hreal) (d2 : hreal) (h1 : b = (hreal_add a d1)) (h2 : d = (hreal_add c d2)) : True = ((hreal_add b d) = (term16 a c d1 d2)).
Proof. exact (SYM (@lem1322135 b a d1 d c d2 h1 h2)). Qed.
Lemma lem1322137 (b : hreal) (a : hreal) (d1 : hreal) (d : hreal) (c : hreal) (d2 : hreal) (h1 : b = (hreal_add a d1)) (h2 : d = (hreal_add c d2)) : (hreal_add b d) = (term16 a c d1 d2).
Proof. exact (EQ_MP (@lem1322136 b a d1 d c d2 h1 h2) (@lem0)). Qed.
Lemma lem1322138 (b : hreal) (a : hreal) (d1 : hreal) (d : hreal) (c : hreal) (d2 : hreal) (h1 : b = (hreal_add a d1)) (h2 : d = (hreal_add c d2)) : term11 b d a c.
Proof. exact (ex_intro (term22 b d a c) (hreal_add d1 d2) (@lem1322137 b a d1 d c d2 h1 h2)). Qed.
Lemma lem1322139 (b : hreal) (a : hreal) (d : hreal) (c : hreal) (h1 : term7 b a d c) : term3 d c.
Proof. exact (proj2 (@lem1322052 b a d c h1)). Qed.
Lemma lem1322140 (b : hreal) (a : hreal) (d : hreal) (c : hreal) (h1 : term7 b a d c) : term3 b a.
Proof. exact (proj1 (@lem1322052 b a d c h1)). Qed.
Lemma lem1322141 (d : hreal) (c : hreal) (b : hreal) (a : hreal) (d1 : hreal) (h1 : term3 d c) (h2 : b = (hreal_add a d1)) : term11 b d a c.
Proof. exact (ex_elim (@lem1322053 d c h1) (fun d2 : hreal => fun h0 : term23 d c d2 => @lem1322138 b a d1 d c d2 h2 h0)). Qed.
Lemma lem1322142 (b : hreal) (a : hreal) (d : hreal) (c : hreal) (h1 : term3 b a) (h2 : term3 d c) : term11 b d a c.
Proof. exact (ex_elim (@lem1322055 b a h1) (fun d1 : hreal => fun h0 : term23 b a d1 => @lem1322141 d c b a d1 h2 h0)). Qed.
Lemma lem1322143 (b : hreal) (a : hreal) (d : hreal) (c : hreal) (h1 : term3 b a) (h2 : term7 b a d c) : (term3 d c) = (term11 b d a c).
Proof. exact (prop_ext (fun h3 : term3 d c => @lem1322142 b a d c h1 h3) (fun h3 : term11 b d a c => @lem1322139 b a d c h2)). Qed.
Lemma lem1322144 (b : hreal) (a : hreal) (d : hreal) (c : hreal) (h1 : term3 b a) (h2 : term7 b a d c) : term11 b d a c.
Proof. exact (EQ_MP (@lem1322143 b a d c h1 h2) (@lem1322139 b a d c h2)). Qed.
Lemma lem1322145 (b : hreal) (a : hreal) (d : hreal) (c : hreal) (h1 : term7 b a d c) : (term3 b a) = (term11 b d a c).
Proof. exact (prop_ext (fun h2 : term3 b a => @lem1322144 b a d c h2 h1) (fun h2 : term11 b d a c => @lem1322140 b a d c h1)). Qed.
Lemma lem1322146 (b : hreal) (a : hreal) (d : hreal) (c : hreal) (h1 : term7 b a d c) : term11 b d a c.
Proof. exact (EQ_MP (@lem1322145 b a d c h1) (@lem1322140 b a d c h1)). Qed.
Lemma lem1322147 (b : hreal) (d : hreal) (a : hreal) (c : hreal) : term13 b d a c.
Proof. exact (fun h0 : term7 b a d c => @lem1322146 b a d c h0). Qed.
Lemma lem1322148 (a : hreal) (c : hreal) (b : hreal) (d : hreal) : term12 a c b d.
Proof. exact (EQ_MP (@lem1322051 a c b d) (@lem1322147 b d a c)). Qed.
Lemma lem1322153 (a : hreal) (c : hreal) (b : hreal) : term24 a c b.
Proof. exact (fun d : hreal => @lem1322148 a c b d). Qed.
Lemma lem1322158 (a : hreal) (b : hreal) : term25 a b.
Proof. exact (fun c : hreal => @lem1322153 a c b). Qed.
Lemma lem1322163 (a : hreal) : term26 a.
Proof. exact (fun b : hreal => @lem1322158 a b). Qed.
Lemma lem1322168 : term27.
Proof. exact (fun a : hreal => @lem1322163 a). Qed.
