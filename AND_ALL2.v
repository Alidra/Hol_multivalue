Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import AND_ALL2_term_abbrevs.
Require Import ALL2_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm1094346_spec.
Require Import thm1094347_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1842_spec.
Require Import thm1844_spec.
Require Import thm1855_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm585_spec.
Require Import thm586_spec.
Require Import thm616_spec.
Require Import thm617_spec.
Lemma lem1164051 {_27428 _27429 : Type'} (P : type1470 _27428 _27429) (Q : type1470 _27428 _27429) (l : list _27429) (m : list _27428) (h1 : (term0 _27428 _27429 P Q l m) = (term1 _27428 _27429 P Q l m)) : (term0 _27428 _27429 P Q l m) = (term1 _27428 _27429 P Q l m).
Proof. exact (h1). Qed.
Lemma lem1164052 {_27428 _27429 : Type'} (P : type1470 _27428 _27429) (Q : type1470 _27428 _27429) (l : list _27429) (m : list _27428) (h1 : (term0 _27428 _27429 P Q l m) = (term1 _27428 _27429 P Q l m)) : (term1 _27428 _27429 P Q l m) = (term0 _27428 _27429 P Q l m).
Proof. exact (SYM (@lem1164051 _27428 _27429 P Q l m h1)). Qed.
Lemma lem1164053 {_27428 _27429 : Type'} (P : type1470 _27428 _27429) (Q : type1470 _27428 _27429) (l : list _27429) (m : list _27428) (h1 : (term1 _27428 _27429 P Q l m) = (term0 _27428 _27429 P Q l m)) : (term1 _27428 _27429 P Q l m) = (term0 _27428 _27429 P Q l m).
Proof. exact (h1). Qed.
Lemma lem1164054 {_27428 _27429 : Type'} (P : type1470 _27428 _27429) (Q : type1470 _27428 _27429) (l : list _27429) (m : list _27428) (h1 : (term1 _27428 _27429 P Q l m) = (term0 _27428 _27429 P Q l m)) : (term0 _27428 _27429 P Q l m) = (term1 _27428 _27429 P Q l m).
Proof. exact (SYM (@lem1164053 _27428 _27429 P Q l m h1)). Qed.
Lemma lem1164055 {_27428 _27429 : Type'} (P : type1470 _27428 _27429) (Q : type1470 _27428 _27429) (l : list _27429) (m : list _27428) : ((term0 _27428 _27429 P Q l m) = (term1 _27428 _27429 P Q l m)) = ((term1 _27428 _27429 P Q l m) = (term0 _27428 _27429 P Q l m)).
Proof. exact (prop_ext (fun h1 : (term0 _27428 _27429 P Q l m) = (term1 _27428 _27429 P Q l m) => @lem1164052 _27428 _27429 P Q l m h1) (fun h1 : (term1 _27428 _27429 P Q l m) = (term0 _27428 _27429 P Q l m) => @lem1164054 _27428 _27429 P Q l m h1)). Qed.
Lemma lem1164056 {_27428 _27429 : Type'} (P : type1470 _27428 _27429) (Q : type1470 _27428 _27429) (l : list _27429) : (term2 _27428 _27429 P Q l) = (term3 _27428 _27429 P Q l).
Proof. exact (fun_ext (fun m : list _27428 => @lem1164055 _27428 _27429 P Q l m)). Qed.
Lemma lem1164057 {_27428 : Type'} : (@all (list _27428)) = (@all (list _27428)).
Proof. exact (eq_refl (@all (list _27428))). Qed.
Lemma lem1164058 {_27428 _27429 : Type'} (P : type1470 _27428 _27429) (Q : type1470 _27428 _27429) (l : list _27429) : (term4 _27428 _27429 P Q l) = (term5 _27428 _27429 P Q l).
Proof. exact (MK_COMB (@lem1164057 _27428) (@lem1164056 _27428 _27429 P Q l)). Qed.
Lemma lem1164059 {_27428 _27429 : Type'} (P : type1470 _27428 _27429) (Q : type1470 _27428 _27429) : (term6 _27428 _27429 P Q) = (term7 _27428 _27429 P Q).
Proof. exact (fun_ext (fun l : list _27429 => @lem1164058 _27428 _27429 P Q l)). Qed.
Lemma lem1164060 {_27429 : Type'} : (@all (list _27429)) = (@all (list _27429)).
Proof. exact (eq_refl (@all (list _27429))). Qed.
Lemma lem1164061 {_27428 _27429 : Type'} (P : type1470 _27428 _27429) (Q : type1470 _27428 _27429) : (term8 _27428 _27429 P Q) = (term9 _27428 _27429 P Q).
Proof. exact (MK_COMB (@lem1164060 _27429) (@lem1164059 _27428 _27429 P Q)). Qed.
Lemma lem1164062 {_27428 _27429 : Type'} (P : type1470 _27428 _27429) (Q : type1470 _27428 _27429) : (term9 _27428 _27429 P Q) = (term8 _27428 _27429 P Q).
Proof. exact (SYM (@lem1164061 _27428 _27429 P Q)). Qed.
Lemma lem1164064 {A : Type'} (P : type1143 A) : term10 A P.
Proof. exact (EQ_MP (@lem1094347 A P) (@lem1094346 A P)). Qed.
Lemma lem1164065 {_27429 : Type'} (P : type1143 _27429) : term10 _27429 P.
Proof. exact (@lem1164064 _27429 P). Qed.
Lemma lem1164066 {_27428 _27429 : Type'} (P : type1470 _27428 _27429) (Q : type1470 _27428 _27429) : term11 _27428 _27429 P Q.
Proof. exact (@lem1164065 _27429 (term7 _27428 _27429 P Q)). Qed.
Lemma lem1164067 {_27428 _27429 : Type'} (P : type1470 _27428 _27429) (Q : type1470 _27428 _27429) : (term12 _27428 _27429 P Q) = (term13 _27428 _27429 P Q).
Proof. exact (eq_refl (term12 _27428 _27429 P Q)). Qed.
Lemma lem1164068 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1164069 {_27428 _27429 : Type'} (P : type1470 _27428 _27429) (Q : type1470 _27428 _27429) : (term14 _27428 _27429 P Q) = (term15 _27428 _27429 P Q).
Proof. exact (MK_COMB (@lem1164068) (@lem1164067 _27428 _27429 P Q)). Qed.
Lemma lem1164070 {_27428 _27429 : Type'} (P : type1470 _27428 _27429) (Q : type1470 _27428 _27429) (t : list _27429) : (term16 _27428 _27429 P Q t) = (term5 _27428 _27429 P Q t).
Proof. exact (eq_refl (term16 _27428 _27429 P Q t)). Qed.
Lemma lem1164071 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1164072 {_27428 _27429 : Type'} (P : type1470 _27428 _27429) (Q : type1470 _27428 _27429) (t : list _27429) : (term17 _27428 _27429 P Q t) = (term18 _27428 _27429 P Q t).
Proof. exact (MK_COMB (@lem1164071) (@lem1164070 _27428 _27429 P Q t)). Qed.
Lemma lem1164073 {_27428 _27429 : Type'} (P : type1470 _27428 _27429) (Q : type1470 _27428 _27429) (h : _27429) (t : list _27429) : (term19 _27428 _27429 P Q h t) = (term20 _27428 _27429 P Q h t).
Proof. exact (eq_refl (term19 _27428 _27429 P Q h t)). Qed.
Lemma lem1164074 {_27428 _27429 : Type'} (P : type1470 _27428 _27429) (Q : type1470 _27428 _27429) (h : _27429) (t : list _27429) : (term21 _27428 _27429 P Q h t) = (term22 _27428 _27429 P Q h t).
Proof. exact (MK_COMB (@lem1164072 _27428 _27429 P Q t) (@lem1164073 _27428 _27429 P Q h t)). Qed.
Lemma lem1164075 {_27428 _27429 : Type'} (P : type1470 _27428 _27429) (Q : type1470 _27428 _27429) (h : _27429) : (term23 _27428 _27429 P Q h) = (term24 _27428 _27429 P Q h).
Proof. exact (fun_ext (fun t : list _27429 => @lem1164074 _27428 _27429 P Q h t)). Qed.
Lemma lem1164076 {_27429 : Type'} : (@all (list _27429)) = (@all (list _27429)).
Proof. exact (eq_refl (@all (list _27429))). Qed.
Lemma lem1164077 {_27428 _27429 : Type'} (P : type1470 _27428 _27429) (Q : type1470 _27428 _27429) (h : _27429) : (term25 _27428 _27429 P Q h) = (term26 _27428 _27429 P Q h).
Proof. exact (MK_COMB (@lem1164076 _27429) (@lem1164075 _27428 _27429 P Q h)). Qed.
Lemma lem1164078 {_27428 _27429 : Type'} (P : type1470 _27428 _27429) (Q : type1470 _27428 _27429) : (term27 _27428 _27429 P Q) = (term28 _27428 _27429 P Q).
Proof. exact (fun_ext (fun h : _27429 => @lem1164077 _27428 _27429 P Q h)). Qed.
Lemma lem1164079 {_27429 : Type'} : (@all _27429) = (@all _27429).
Proof. exact (eq_refl (@all _27429)). Qed.
Lemma lem1164080 {_27428 _27429 : Type'} (P : type1470 _27428 _27429) (Q : type1470 _27428 _27429) : (term29 _27428 _27429 P Q) = (term30 _27428 _27429 P Q).
Proof. exact (MK_COMB (@lem1164079 _27429) (@lem1164078 _27428 _27429 P Q)). Qed.
Lemma lem1164081 {_27428 _27429 : Type'} (P : type1470 _27428 _27429) (Q : type1470 _27428 _27429) : (term31 _27428 _27429 P Q) = (term32 _27428 _27429 P Q).
Proof. exact (MK_COMB (@lem1164069 _27428 _27429 P Q) (@lem1164080 _27428 _27429 P Q)). Qed.
Lemma lem1164082 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1164083 {_27428 _27429 : Type'} (P : type1470 _27428 _27429) (Q : type1470 _27428 _27429) : (term33 _27428 _27429 P Q) = (term34 _27428 _27429 P Q).
Proof. exact (MK_COMB (@lem1164082) (@lem1164081 _27428 _27429 P Q)). Qed.
Lemma lem1164084 {_27428 _27429 : Type'} (P : type1470 _27428 _27429) (Q : type1470 _27428 _27429) (l : list _27429) : (term16 _27428 _27429 P Q l) = (term5 _27428 _27429 P Q l).
Proof. exact (eq_refl (term16 _27428 _27429 P Q l)). Qed.
Lemma lem1164085 {_27428 _27429 : Type'} (P : type1470 _27428 _27429) (Q : type1470 _27428 _27429) : (term35 _27428 _27429 P Q) = (term7 _27428 _27429 P Q).
Proof. exact (fun_ext (fun l : list _27429 => @lem1164084 _27428 _27429 P Q l)). Qed.
Lemma lem1164086 {_27429 : Type'} : (@all (list _27429)) = (@all (list _27429)).
Proof. exact (eq_refl (@all (list _27429))). Qed.
Lemma lem1164087 {_27428 _27429 : Type'} (P : type1470 _27428 _27429) (Q : type1470 _27428 _27429) : (term36 _27428 _27429 P Q) = (term9 _27428 _27429 P Q).
Proof. exact (MK_COMB (@lem1164086 _27429) (@lem1164085 _27428 _27429 P Q)). Qed.
Lemma lem1164088 {_27428 _27429 : Type'} (P : type1470 _27428 _27429) (Q : type1470 _27428 _27429) : (term11 _27428 _27429 P Q) = (term37 _27428 _27429 P Q).
Proof. exact (MK_COMB (@lem1164083 _27428 _27429 P Q) (@lem1164087 _27428 _27429 P Q)). Qed.
Lemma lem1164089 {_27428 _27429 : Type'} (P : type1470 _27428 _27429) (Q : type1470 _27428 _27429) : term37 _27428 _27429 P Q.
Proof. exact (EQ_MP (@lem1164088 _27428 _27429 P Q) (@lem1164066 _27428 _27429 P Q)). Qed.
Lemma lem1164090 {_27428 _27429 : Type'} (P : type1470 _27428 _27429) (Q : type1470 _27428 _27429) (t : list _27429) (h1 : term5 _27428 _27429 P Q t) : term5 _27428 _27429 P Q t.
Proof. exact (h1). Qed.
Lemma lem1164092 {A : Type'} (P : type1143 A) : term10 A P.
Proof. exact (EQ_MP (@lem1094347 A P) (@lem1094346 A P)). Qed.
Lemma lem1164093 {_27428 : Type'} (P : type1143 _27428) : term10 _27428 P.
Proof. exact (@lem1164092 _27428 P). Qed.
Lemma lem1164094 {_27428 _27429 : Type'} (P : type1470 _27428 _27429) (Q : type1470 _27428 _27429) : term38 _27428 _27429 P Q.
Proof. exact (@lem1164093 _27428 (term39 _27428 _27429 P Q)). Qed.
Lemma lem1164095 {_27428 _27429 : Type'} (P : type1470 _27428 _27429) (Q : type1470 _27428 _27429) : (term40 _27428 _27429 P Q) = ((term41 _27428 _27429 P Q) = (term42 _27428 _27429 P Q)).
Proof. exact (eq_refl (term40 _27428 _27429 P Q)). Qed.
Lemma lem1164096 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1164097 {_27428 _27429 : Type'} (P : type1470 _27428 _27429) (Q : type1470 _27428 _27429) : (term43 _27428 _27429 P Q) = (term44 _27428 _27429 P Q).
Proof. exact (MK_COMB (@lem1164096) (@lem1164095 _27428 _27429 P Q)). Qed.
Lemma lem1164098 {_27428 _27429 : Type'} (P : type1470 _27428 _27429) (Q : type1470 _27428 _27429) (t : list _27428) : (term45 _27428 _27429 P Q t) = ((term46 _27428 _27429 P Q t) = (term47 _27428 _27429 P Q t)).
Proof. exact (eq_refl (term45 _27428 _27429 P Q t)). Qed.
Lemma lem1164099 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1164100 {_27428 _27429 : Type'} (P : type1470 _27428 _27429) (Q : type1470 _27428 _27429) (t : list _27428) : (term48 _27428 _27429 P Q t) = (term49 _27428 _27429 P Q t).
Proof. exact (MK_COMB (@lem1164099) (@lem1164098 _27428 _27429 P Q t)). Qed.
Lemma lem1164101 {_27428 _27429 : Type'} (P : type1470 _27428 _27429) (Q : type1470 _27428 _27429) (h : _27428) (t : list _27428) : (term50 _27428 _27429 P Q h t) = ((term51 _27428 _27429 P Q h t) = (term52 _27428 _27429 P Q h t)).
Proof. exact (eq_refl (term50 _27428 _27429 P Q h t)). Qed.
Lemma lem1164102 {_27428 _27429 : Type'} (P : type1470 _27428 _27429) (Q : type1470 _27428 _27429) (h : _27428) (t : list _27428) : (term53 _27428 _27429 P Q h t) = (term54 _27428 _27429 P Q h t).
Proof. exact (MK_COMB (@lem1164100 _27428 _27429 P Q t) (@lem1164101 _27428 _27429 P Q h t)). Qed.
Lemma lem1164103 {_27428 _27429 : Type'} (P : type1470 _27428 _27429) (Q : type1470 _27428 _27429) (h : _27428) : (term55 _27428 _27429 P Q h) = (term56 _27428 _27429 P Q h).
Proof. exact (fun_ext (fun t : list _27428 => @lem1164102 _27428 _27429 P Q h t)). Qed.
Lemma lem1164104 {_27428 : Type'} : (@all (list _27428)) = (@all (list _27428)).
Proof. exact (eq_refl (@all (list _27428))). Qed.
Lemma lem1164105 {_27428 _27429 : Type'} (P : type1470 _27428 _27429) (Q : type1470 _27428 _27429) (h : _27428) : (term57 _27428 _27429 P Q h) = (term58 _27428 _27429 P Q h).
Proof. exact (MK_COMB (@lem1164104 _27428) (@lem1164103 _27428 _27429 P Q h)). Qed.
Lemma lem1164106 {_27428 _27429 : Type'} (P : type1470 _27428 _27429) (Q : type1470 _27428 _27429) : (term59 _27428 _27429 P Q) = (term60 _27428 _27429 P Q).
Proof. exact (fun_ext (fun h : _27428 => @lem1164105 _27428 _27429 P Q h)). Qed.
Lemma lem1164107 {_27428 : Type'} : (@all _27428) = (@all _27428).
Proof. exact (eq_refl (@all _27428)). Qed.
Lemma lem1164108 {_27428 _27429 : Type'} (P : type1470 _27428 _27429) (Q : type1470 _27428 _27429) : (term61 _27428 _27429 P Q) = (term62 _27428 _27429 P Q).
Proof. exact (MK_COMB (@lem1164107 _27428) (@lem1164106 _27428 _27429 P Q)). Qed.
Lemma lem1164109 {_27428 _27429 : Type'} (P : type1470 _27428 _27429) (Q : type1470 _27428 _27429) : (term63 _27428 _27429 P Q) = (term64 _27428 _27429 P Q).
Proof. exact (MK_COMB (@lem1164097 _27428 _27429 P Q) (@lem1164108 _27428 _27429 P Q)). Qed.
Lemma lem1164110 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1164111 {_27428 _27429 : Type'} (P : type1470 _27428 _27429) (Q : type1470 _27428 _27429) : (term65 _27428 _27429 P Q) = (term66 _27428 _27429 P Q).
Proof. exact (MK_COMB (@lem1164110) (@lem1164109 _27428 _27429 P Q)). Qed.
Lemma lem1164112 {_27428 _27429 : Type'} (P : type1470 _27428 _27429) (Q : type1470 _27428 _27429) (m : list _27428) : (term45 _27428 _27429 P Q m) = ((term46 _27428 _27429 P Q m) = (term47 _27428 _27429 P Q m)).
Proof. exact (eq_refl (term45 _27428 _27429 P Q m)). Qed.
Lemma lem1164113 {_27428 _27429 : Type'} (P : type1470 _27428 _27429) (Q : type1470 _27428 _27429) : (term67 _27428 _27429 P Q) = (term39 _27428 _27429 P Q).
Proof. exact (fun_ext (fun m : list _27428 => @lem1164112 _27428 _27429 P Q m)). Qed.
Lemma lem1164114 {_27428 : Type'} : (@all (list _27428)) = (@all (list _27428)).
Proof. exact (eq_refl (@all (list _27428))). Qed.
Lemma lem1164115 {_27428 _27429 : Type'} (P : type1470 _27428 _27429) (Q : type1470 _27428 _27429) : (term68 _27428 _27429 P Q) = (term13 _27428 _27429 P Q).
Proof. exact (MK_COMB (@lem1164114 _27428) (@lem1164113 _27428 _27429 P Q)). Qed.
Lemma lem1164116 {_27428 _27429 : Type'} (P : type1470 _27428 _27429) (Q : type1470 _27428 _27429) : (term38 _27428 _27429 P Q) = (term69 _27428 _27429 P Q).
Proof. exact (MK_COMB (@lem1164111 _27428 _27429 P Q) (@lem1164115 _27428 _27429 P Q)). Qed.
Lemma lem1164117 {_27428 _27429 : Type'} (P : type1470 _27428 _27429) (Q : type1470 _27428 _27429) : term69 _27428 _27429 P Q.
Proof. exact (EQ_MP (@lem1164116 _27428 _27429 P Q) (@lem1164094 _27428 _27429 P Q)). Qed.
Lemma lem1164120 {A : Type'} (P : type1143 A) : term10 A P.
Proof. exact (EQ_MP (@lem1094347 A P) (@lem1094346 A P)). Qed.
Lemma lem1164121 {_27428 : Type'} (P : type1143 _27428) : term10 _27428 P.
Proof. exact (@lem1164120 _27428 P). Qed.
Lemma lem1164122 {_27428 _27429 : Type'} (P : type1470 _27428 _27429) (Q : type1470 _27428 _27429) (h : _27429) (t : list _27429) : term70 _27428 _27429 P Q h t.
Proof. exact (@lem1164121 _27428 (term71 _27428 _27429 P Q h t)). Qed.
Lemma lem1164123 {_27428 _27429 : Type'} (P : type1470 _27428 _27429) (Q : type1470 _27428 _27429) (h : _27429) (t : list _27429) : (term72 _27428 _27429 P Q h t) = ((term73 _27428 _27429 P Q h t) = (term74 _27428 _27429 P Q h t)).
Proof. exact (eq_refl (term72 _27428 _27429 P Q h t)). Qed.
Lemma lem1164124 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1164125 {_27428 _27429 : Type'} (P : type1470 _27428 _27429) (Q : type1470 _27428 _27429) (h : _27429) (t : list _27429) : (term75 _27428 _27429 P Q h t) = (term76 _27428 _27429 P Q h t).
Proof. exact (MK_COMB (@lem1164124) (@lem1164123 _27428 _27429 P Q h t)). Qed.
Lemma lem1164126 {_27428 _27429 : Type'} (P : type1470 _27428 _27429) (Q : type1470 _27428 _27429) (h : _27429) (t : list _27429) (t' : list _27428) : (term77 _27428 _27429 P Q h t t') = ((term78 _27428 _27429 P Q h t t') = (term79 _27428 _27429 P Q h t t')).
Proof. exact (eq_refl (term77 _27428 _27429 P Q h t t')). Qed.
Lemma lem1164127 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1164128 {_27428 _27429 : Type'} (P : type1470 _27428 _27429) (Q : type1470 _27428 _27429) (h : _27429) (t : list _27429) (t' : list _27428) : (term80 _27428 _27429 P Q h t t') = (term81 _27428 _27429 P Q h t t').
Proof. exact (MK_COMB (@lem1164127) (@lem1164126 _27428 _27429 P Q h t t')). Qed.
Lemma lem1164129 {_27428 _27429 : Type'} (P : type1470 _27428 _27429) (Q : type1470 _27428 _27429) (h : _27429) (t : list _27429) (h' : _27428) (t' : list _27428) : (term82 _27428 _27429 P Q h t h' t') = ((term83 _27428 _27429 P Q h t h' t') = (term84 _27428 _27429 P Q h t h' t')).
Proof. exact (eq_refl (term82 _27428 _27429 P Q h t h' t')). Qed.
Lemma lem1164130 {_27428 _27429 : Type'} (P : type1470 _27428 _27429) (Q : type1470 _27428 _27429) (h : _27429) (t : list _27429) (h' : _27428) (t' : list _27428) : (term85 _27428 _27429 P Q h t h' t') = (term86 _27428 _27429 P Q h t h' t').
Proof. exact (MK_COMB (@lem1164128 _27428 _27429 P Q h t t') (@lem1164129 _27428 _27429 P Q h t h' t')). Qed.
Lemma lem1164131 {_27428 _27429 : Type'} (P : type1470 _27428 _27429) (Q : type1470 _27428 _27429) (h : _27429) (t : list _27429) (h' : _27428) : (term87 _27428 _27429 P Q h t h') = (term88 _27428 _27429 P Q h t h').
Proof. exact (fun_ext (fun t' : list _27428 => @lem1164130 _27428 _27429 P Q h t h' t')). Qed.
Lemma lem1164132 {_27428 : Type'} : (@all (list _27428)) = (@all (list _27428)).
Proof. exact (eq_refl (@all (list _27428))). Qed.
Lemma lem1164133 {_27428 _27429 : Type'} (P : type1470 _27428 _27429) (Q : type1470 _27428 _27429) (h : _27429) (t : list _27429) (h' : _27428) : (term89 _27428 _27429 P Q h t h') = (term90 _27428 _27429 P Q h t h').
Proof. exact (MK_COMB (@lem1164132 _27428) (@lem1164131 _27428 _27429 P Q h t h')). Qed.
Lemma lem1164134 {_27428 _27429 : Type'} (P : type1470 _27428 _27429) (Q : type1470 _27428 _27429) (h : _27429) (t : list _27429) : (term91 _27428 _27429 P Q h t) = (term92 _27428 _27429 P Q h t).
Proof. exact (fun_ext (fun h' : _27428 => @lem1164133 _27428 _27429 P Q h t h')). Qed.
Lemma lem1164135 {_27428 : Type'} : (@all _27428) = (@all _27428).
Proof. exact (eq_refl (@all _27428)). Qed.
Lemma lem1164136 {_27428 _27429 : Type'} (P : type1470 _27428 _27429) (Q : type1470 _27428 _27429) (h : _27429) (t : list _27429) : (term93 _27428 _27429 P Q h t) = (term94 _27428 _27429 P Q h t).
Proof. exact (MK_COMB (@lem1164135 _27428) (@lem1164134 _27428 _27429 P Q h t)). Qed.
Lemma lem1164137 {_27428 _27429 : Type'} (P : type1470 _27428 _27429) (Q : type1470 _27428 _27429) (h : _27429) (t : list _27429) : (term95 _27428 _27429 P Q h t) = (term96 _27428 _27429 P Q h t).
Proof. exact (MK_COMB (@lem1164125 _27428 _27429 P Q h t) (@lem1164136 _27428 _27429 P Q h t)). Qed.
Lemma lem1164138 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1164139 {_27428 _27429 : Type'} (P : type1470 _27428 _27429) (Q : type1470 _27428 _27429) (h : _27429) (t : list _27429) : (term97 _27428 _27429 P Q h t) = (term98 _27428 _27429 P Q h t).
Proof. exact (MK_COMB (@lem1164138) (@lem1164137 _27428 _27429 P Q h t)). Qed.
Lemma lem1164140 {_27428 _27429 : Type'} (P : type1470 _27428 _27429) (Q : type1470 _27428 _27429) (h : _27429) (t : list _27429) (m : list _27428) : (term77 _27428 _27429 P Q h t m) = ((term78 _27428 _27429 P Q h t m) = (term79 _27428 _27429 P Q h t m)).
Proof. exact (eq_refl (term77 _27428 _27429 P Q h t m)). Qed.
Lemma lem1164141 {_27428 _27429 : Type'} (P : type1470 _27428 _27429) (Q : type1470 _27428 _27429) (h : _27429) (t : list _27429) : (term99 _27428 _27429 P Q h t) = (term71 _27428 _27429 P Q h t).
Proof. exact (fun_ext (fun m : list _27428 => @lem1164140 _27428 _27429 P Q h t m)). Qed.
Lemma lem1164142 {_27428 : Type'} : (@all (list _27428)) = (@all (list _27428)).
Proof. exact (eq_refl (@all (list _27428))). Qed.
Lemma lem1164143 {_27428 _27429 : Type'} (P : type1470 _27428 _27429) (Q : type1470 _27428 _27429) (h : _27429) (t : list _27429) : (term100 _27428 _27429 P Q h t) = (term20 _27428 _27429 P Q h t).
Proof. exact (MK_COMB (@lem1164142 _27428) (@lem1164141 _27428 _27429 P Q h t)). Qed.
Lemma lem1164144 {_27428 _27429 : Type'} (P : type1470 _27428 _27429) (Q : type1470 _27428 _27429) (h : _27429) (t : list _27429) : (term70 _27428 _27429 P Q h t) = (term101 _27428 _27429 P Q h t).
Proof. exact (MK_COMB (@lem1164139 _27428 _27429 P Q h t) (@lem1164143 _27428 _27429 P Q h t)). Qed.
Lemma lem1164145 {_27428 _27429 : Type'} (P : type1470 _27428 _27429) (Q : type1470 _27428 _27429) (h : _27429) (t : list _27429) : term101 _27428 _27429 P Q h t.
Proof. exact (EQ_MP (@lem1164144 _27428 _27429 P Q h t) (@lem1164122 _27428 _27429 P Q h t)). Qed.
Lemma lem1164156 {_25470 _25471 : Type'} (P : type1470 _25470 _25471) : (@ALL2 _25471 _25470 P (@nil _25471) (@nil _25470)) = True.
Proof. exact (proj1 (@lem1104212 _25470 _25471 (@el _25471) (@el _25470) P (@el (list _25471)) (@el (list _25470)))). Qed.
Lemma lem1164157 {_27428 _27429 : Type'} (P : type1470 _27428 _27429) : (@ALL2 _27429 _27428 P (@nil _27429) (@nil _27428)) = True.
Proof. exact (@lem1164156 _27428 _27429 P). Qed.
Lemma lem1164158 {_27428 _27429 : Type'} (P : type1470 _27428 _27429) (Q : type1470 _27428 _27429) : (term41 _27428 _27429 P Q) = True.
Proof. exact (@lem1164157 _27428 _27429 (term102 _27428 _27429 P Q)). Qed.
Lemma lem1164159 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1164160 {_27428 _27429 : Type'} (P : type1470 _27428 _27429) (Q : type1470 _27428 _27429) : (term103 _27428 _27429 P Q) = (@eq Prop True).
Proof. exact (MK_COMB (@lem1164159) (@lem1164158 _27428 _27429 P Q)). Qed.
Lemma lem1164164 {_25470 _25471 : Type'} (P : type1470 _25470 _25471) : (@ALL2 _25471 _25470 P (@nil _25471) (@nil _25470)) = True.
Proof. exact (proj1 (@lem1104212 _25470 _25471 (@el _25471) (@el _25470) P (@el (list _25471)) (@el (list _25470)))). Qed.
Lemma lem1164165 {_27428 _27429 : Type'} (P : type1470 _27428 _27429) : (@ALL2 _27429 _27428 P (@nil _27429) (@nil _27428)) = True.
Proof. exact (@lem1164164 _27428 _27429 P). Qed.
Lemma lem1164166 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1164167 {_27428 _27429 : Type'} (P : type1470 _27428 _27429) : (term104 _27428 _27429 P) = (and True).
Proof. exact (MK_COMB (@lem1164166) (@lem1164165 _27428 _27429 P)). Qed.
Lemma lem1164169 {_25470 _25471 : Type'} (P : type1470 _25470 _25471) : (@ALL2 _25471 _25470 P (@nil _25471) (@nil _25470)) = True.
Proof. exact (proj1 (@lem1104212 _25470 _25471 (@el _25471) (@el _25470) P (@el (list _25471)) (@el (list _25470)))). Qed.
Lemma lem1164170 {_27428 _27429 : Type'} (P : type1470 _27428 _27429) : (@ALL2 _27429 _27428 P (@nil _27429) (@nil _27428)) = True.
Proof. exact (@lem1164169 _27428 _27429 P). Qed.
Lemma lem1164171 {_27428 _27429 : Type'} (Q : type1470 _27428 _27429) : (@ALL2 _27429 _27428 Q (@nil _27429) (@nil _27428)) = True.
Proof. exact (@lem1164170 _27428 _27429 Q). Qed.
Lemma lem1164172 {_27428 _27429 : Type'} (P : type1470 _27428 _27429) (Q : type1470 _27428 _27429) : (term42 _27428 _27429 P Q) = (True /\ True).
Proof. exact (MK_COMB (@lem1164167 _27428 _27429 P) (@lem1164171 _27428 _27429 Q)). Qed.
Lemma lem1164174 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1164175 : (True /\ True) = True.
Proof. exact (@lem1164174 True). Qed.
Lemma lem1164176 {_27428 _27429 : Type'} (P : type1470 _27428 _27429) (Q : type1470 _27428 _27429) : (term42 _27428 _27429 P Q) = True.
Proof. exact (TRANS (@lem1164172 _27428 _27429 P Q) (@lem1164175)). Qed.
Lemma lem1164177 {_27428 _27429 : Type'} (P : type1470 _27428 _27429) (Q : type1470 _27428 _27429) : ((term41 _27428 _27429 P Q) = (term42 _27428 _27429 P Q)) = (True = True).
Proof. exact (MK_COMB (@lem1164160 _27428 _27429 P Q) (@lem1164176 _27428 _27429 P Q)). Qed.
Lemma lem1164179 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem1164180 : (True = True) = True.
Proof. exact (@lem1164179 True). Qed.
Lemma lem1164181 {_27428 _27429 : Type'} (P : type1470 _27428 _27429) (Q : type1470 _27428 _27429) : ((term41 _27428 _27429 P Q) = (term42 _27428 _27429 P Q)) = True.
Proof. exact (TRANS (@lem1164177 _27428 _27429 P Q) (@lem1164180)). Qed.
Lemma lem1164182 {_27428 _27429 : Type'} (P : type1470 _27428 _27429) (Q : type1470 _27428 _27429) : True = ((term41 _27428 _27429 P Q) = (term42 _27428 _27429 P Q)).
Proof. exact (SYM (@lem1164181 _27428 _27429 P Q)). Qed.
Lemma lem1164183 {_27428 _27429 : Type'} (P : type1470 _27428 _27429) (Q : type1470 _27428 _27429) : (term41 _27428 _27429 P Q) = (term42 _27428 _27429 P Q).
Proof. exact (EQ_MP (@lem1164182 _27428 _27429 P Q) (@lem0)). Qed.
Lemma lem1164184 {_25470 _25471 : Type'} (h1' : _25471) (h2' : _25470) (P : type1470 _25470 _25471) (t1 : list _25471) (t2 : list _25470) : term105 _25470 _25471 h1' h2' P t1 t2.
Proof. exact (proj2 (@lem1104212 _25470 _25471 h1' h2' P t1 t2)). Qed.
Lemma lem1164185 {_25470 _25471 : Type'} (h1' : _25471) (h2' : _25470) (P : type1470 _25470 _25471) (t1 : list _25471) (t2 : list _25470) : term106 _25470 _25471 h1' h2' P t1 t2.
Proof. exact (proj2 (@lem1164184 _25470 _25471 h1' h2' P t1 t2)). Qed.
Lemma lem1164193 {_25470 _25471 : Type'} (P : type1470 _25470 _25471) (h2' : _25470) (t2 : list _25470) : (term107 _25470 _25471 P h2' t2) = False.
Proof. exact (proj1 (@lem1164185 _25470 _25471 (@el _25471) h2' P (@el (list _25471)) t2)). Qed.
Lemma lem1164194 {_27428 _27429 : Type'} (P : type1470 _27428 _27429) (h2' : _27428) (t2 : list _27428) : (term107 _27428 _27429 P h2' t2) = False.
Proof. exact (@lem1164193 _27428 _27429 P h2' t2). Qed.
Lemma lem1164195 {_27428 _27429 : Type'} (P : type1470 _27428 _27429) (Q : type1470 _27428 _27429) (h : _27428) (t : list _27428) : (term51 _27428 _27429 P Q h t) = False.
Proof. exact (@lem1164194 _27428 _27429 (term102 _27428 _27429 P Q) h t). Qed.
Lemma lem1164196 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1164197 {_27428 _27429 : Type'} (P : type1470 _27428 _27429) (Q : type1470 _27428 _27429) (h : _27428) (t : list _27428) : (term108 _27428 _27429 P Q h t) = (@eq Prop False).
Proof. exact (MK_COMB (@lem1164196) (@lem1164195 _27428 _27429 P Q h t)). Qed.
Lemma lem1164201 {_25470 _25471 : Type'} (P : type1470 _25470 _25471) (h2' : _25470) (t2 : list _25470) : (term107 _25470 _25471 P h2' t2) = False.
Proof. exact (proj1 (@lem1164185 _25470 _25471 (@el _25471) h2' P (@el (list _25471)) t2)). Qed.
Lemma lem1164202 {_27428 _27429 : Type'} (P : type1470 _27428 _27429) (h2' : _27428) (t2 : list _27428) : (term107 _27428 _27429 P h2' t2) = False.
Proof. exact (@lem1164201 _27428 _27429 P h2' t2). Qed.
Lemma lem1164203 {_27428 _27429 : Type'} (P : type1470 _27428 _27429) (h : _27428) (t : list _27428) : (term107 _27428 _27429 P h t) = False.
Proof. exact (@lem1164202 _27428 _27429 P h t). Qed.
Lemma lem1164204 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1164205 {_27428 _27429 : Type'} (P : type1470 _27428 _27429) (h : _27428) (t : list _27428) : (term109 _27428 _27429 P h t) = (and False).
Proof. exact (MK_COMB (@lem1164204) (@lem1164203 _27428 _27429 P h t)). Qed.
Lemma lem1164207 {_25470 _25471 : Type'} (P : type1470 _25470 _25471) (h2' : _25470) (t2 : list _25470) : (term107 _25470 _25471 P h2' t2) = False.
Proof. exact (proj1 (@lem1164185 _25470 _25471 (@el _25471) h2' P (@el (list _25471)) t2)). Qed.
Lemma lem1164208 {_27428 _27429 : Type'} (P : type1470 _27428 _27429) (h2' : _27428) (t2 : list _27428) : (term107 _27428 _27429 P h2' t2) = False.
Proof. exact (@lem1164207 _27428 _27429 P h2' t2). Qed.
Lemma lem1164209 {_27428 _27429 : Type'} (Q : type1470 _27428 _27429) (h : _27428) (t : list _27428) : (term107 _27428 _27429 Q h t) = False.
Proof. exact (@lem1164208 _27428 _27429 Q h t). Qed.
Lemma lem1164210 {_27428 _27429 : Type'} (P : type1470 _27428 _27429) (Q : type1470 _27428 _27429) (h : _27428) (t : list _27428) : (term52 _27428 _27429 P Q h t) = (False /\ False).
Proof. exact (MK_COMB (@lem1164205 _27428 _27429 P h t) (@lem1164209 _27428 _27429 Q h t)). Qed.
Lemma lem1164212 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem1164213 : (False /\ False) = False.
Proof. exact (@lem1164212 False). Qed.
Lemma lem1164214 {_27428 _27429 : Type'} (P : type1470 _27428 _27429) (Q : type1470 _27428 _27429) (h : _27428) (t : list _27428) : (term52 _27428 _27429 P Q h t) = False.
Proof. exact (TRANS (@lem1164210 _27428 _27429 P Q h t) (@lem1164213)). Qed.
Lemma lem1164215 {_27428 _27429 : Type'} (P : type1470 _27428 _27429) (Q : type1470 _27428 _27429) (h : _27428) (t : list _27428) : ((term51 _27428 _27429 P Q h t) = (term52 _27428 _27429 P Q h t)) = (False = False).
Proof. exact (MK_COMB (@lem1164197 _27428 _27429 P Q h t) (@lem1164214 _27428 _27429 P Q h t)). Qed.
Lemma lem1164217 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem1164218 : (False = False) = (~ False).
Proof. exact (@lem1164217 False). Qed.
Lemma lem1164220 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1164221 : (False = False) = True.
Proof. exact (TRANS (@lem1164218) (@lem1164220)). Qed.
Lemma lem1164222 {_27428 _27429 : Type'} (P : type1470 _27428 _27429) (Q : type1470 _27428 _27429) (h : _27428) (t : list _27428) : ((term51 _27428 _27429 P Q h t) = (term52 _27428 _27429 P Q h t)) = True.
Proof. exact (TRANS (@lem1164215 _27428 _27429 P Q h t) (@lem1164221)). Qed.
Lemma lem1164223 {_27428 _27429 : Type'} (P : type1470 _27428 _27429) (Q : type1470 _27428 _27429) (h : _27428) (t : list _27428) : True = ((term51 _27428 _27429 P Q h t) = (term52 _27428 _27429 P Q h t)).
Proof. exact (SYM (@lem1164222 _27428 _27429 P Q h t)). Qed.
Lemma lem1164224 {_27428 _27429 : Type'} (P : type1470 _27428 _27429) (Q : type1470 _27428 _27429) (h : _27428) (t : list _27428) : (term51 _27428 _27429 P Q h t) = (term52 _27428 _27429 P Q h t).
Proof. exact (EQ_MP (@lem1164223 _27428 _27429 P Q h t) (@lem0)). Qed.
Lemma lem1164225 {_25470 _25471 : Type'} (h1' : _25471) (h2' : _25470) (P : type1470 _25470 _25471) (t1 : list _25471) (t2 : list _25470) : term105 _25470 _25471 h1' h2' P t1 t2.
Proof. exact (proj2 (@lem1104212 _25470 _25471 h1' h2' P t1 t2)). Qed.
Lemma lem1164237 {_25470 _25471 : Type'} (P : type1470 _25470 _25471) (h1' : _25471) (t1 : list _25471) : (term110 _25470 _25471 P h1' t1) = False.
Proof. exact (proj1 (@lem1164225 _25470 _25471 h1' (@el _25470) P t1 (@el (list _25470)))). Qed.
Lemma lem1164238 {_27428 _27429 : Type'} (P : type1470 _27428 _27429) (h1' : _27429) (t1 : list _27429) : (term110 _27428 _27429 P h1' t1) = False.
Proof. exact (@lem1164237 _27428 _27429 P h1' t1). Qed.
Lemma lem1164239 {_27428 _27429 : Type'} (P : type1470 _27428 _27429) (Q : type1470 _27428 _27429) (h : _27429) (t : list _27429) : (term73 _27428 _27429 P Q h t) = False.
Proof. exact (@lem1164238 _27428 _27429 (term102 _27428 _27429 P Q) h t). Qed.
Lemma lem1164240 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1164241 {_27428 _27429 : Type'} (P : type1470 _27428 _27429) (Q : type1470 _27428 _27429) (h : _27429) (t : list _27429) : (term111 _27428 _27429 P Q h t) = (@eq Prop False).
Proof. exact (MK_COMB (@lem1164240) (@lem1164239 _27428 _27429 P Q h t)). Qed.
Lemma lem1164245 {_25470 _25471 : Type'} (P : type1470 _25470 _25471) (h1' : _25471) (t1 : list _25471) : (term110 _25470 _25471 P h1' t1) = False.
Proof. exact (proj1 (@lem1164225 _25470 _25471 h1' (@el _25470) P t1 (@el (list _25470)))). Qed.
Lemma lem1164246 {_27428 _27429 : Type'} (P : type1470 _27428 _27429) (h1' : _27429) (t1 : list _27429) : (term110 _27428 _27429 P h1' t1) = False.
Proof. exact (@lem1164245 _27428 _27429 P h1' t1). Qed.
Lemma lem1164247 {_27428 _27429 : Type'} (P : type1470 _27428 _27429) (h : _27429) (t : list _27429) : (term110 _27428 _27429 P h t) = False.
Proof. exact (@lem1164246 _27428 _27429 P h t). Qed.
Lemma lem1164248 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1164249 {_27428 _27429 : Type'} (P : type1470 _27428 _27429) (h : _27429) (t : list _27429) : (term112 _27428 _27429 P h t) = (and False).
Proof. exact (MK_COMB (@lem1164248) (@lem1164247 _27428 _27429 P h t)). Qed.
Lemma lem1164251 {_25470 _25471 : Type'} (P : type1470 _25470 _25471) (h1' : _25471) (t1 : list _25471) : (term110 _25470 _25471 P h1' t1) = False.
Proof. exact (proj1 (@lem1164225 _25470 _25471 h1' (@el _25470) P t1 (@el (list _25470)))). Qed.
Lemma lem1164252 {_27428 _27429 : Type'} (P : type1470 _27428 _27429) (h1' : _27429) (t1 : list _27429) : (term110 _27428 _27429 P h1' t1) = False.
Proof. exact (@lem1164251 _27428 _27429 P h1' t1). Qed.
Lemma lem1164253 {_27428 _27429 : Type'} (Q : type1470 _27428 _27429) (h : _27429) (t : list _27429) : (term110 _27428 _27429 Q h t) = False.
Proof. exact (@lem1164252 _27428 _27429 Q h t). Qed.
Lemma lem1164254 {_27428 _27429 : Type'} (P : type1470 _27428 _27429) (Q : type1470 _27428 _27429) (h : _27429) (t : list _27429) : (term74 _27428 _27429 P Q h t) = (False /\ False).
Proof. exact (MK_COMB (@lem1164249 _27428 _27429 P h t) (@lem1164253 _27428 _27429 Q h t)). Qed.
Lemma lem1164256 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem1164257 : (False /\ False) = False.
Proof. exact (@lem1164256 False). Qed.
Lemma lem1164258 {_27428 _27429 : Type'} (P : type1470 _27428 _27429) (Q : type1470 _27428 _27429) (h : _27429) (t : list _27429) : (term74 _27428 _27429 P Q h t) = False.
Proof. exact (TRANS (@lem1164254 _27428 _27429 P Q h t) (@lem1164257)). Qed.
Lemma lem1164259 {_27428 _27429 : Type'} (P : type1470 _27428 _27429) (Q : type1470 _27428 _27429) (h : _27429) (t : list _27429) : ((term73 _27428 _27429 P Q h t) = (term74 _27428 _27429 P Q h t)) = (False = False).
Proof. exact (MK_COMB (@lem1164241 _27428 _27429 P Q h t) (@lem1164258 _27428 _27429 P Q h t)). Qed.
Lemma lem1164261 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem1164262 : (False = False) = (~ False).
Proof. exact (@lem1164261 False). Qed.
Lemma lem1164264 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1164265 : (False = False) = True.
Proof. exact (TRANS (@lem1164262) (@lem1164264)). Qed.
Lemma lem1164266 {_27428 _27429 : Type'} (P : type1470 _27428 _27429) (Q : type1470 _27428 _27429) (h : _27429) (t : list _27429) : ((term73 _27428 _27429 P Q h t) = (term74 _27428 _27429 P Q h t)) = True.
Proof. exact (TRANS (@lem1164259 _27428 _27429 P Q h t) (@lem1164265)). Qed.
Lemma lem1164267 {_27428 _27429 : Type'} (P : type1470 _27428 _27429) (Q : type1470 _27428 _27429) (h : _27429) (t : list _27429) : True = ((term73 _27428 _27429 P Q h t) = (term74 _27428 _27429 P Q h t)).
Proof. exact (SYM (@lem1164266 _27428 _27429 P Q h t)). Qed.
Lemma lem1164268 {_27428 _27429 : Type'} (P : type1470 _27428 _27429) (Q : type1470 _27428 _27429) (h : _27429) (t : list _27429) : (term73 _27428 _27429 P Q h t) = (term74 _27428 _27429 P Q h t).
Proof. exact (EQ_MP (@lem1164267 _27428 _27429 P Q h t) (@lem0)). Qed.
Lemma lem1164269 {_25470 _25471 : Type'} (h1' : _25471) (h2' : _25470) (P : type1470 _25470 _25471) (t1 : list _25471) (t2 : list _25470) : term105 _25470 _25471 h1' h2' P t1 t2.
Proof. exact (proj2 (@lem1104212 _25470 _25471 h1' h2' P t1 t2)). Qed.
Lemma lem1164270 {_25470 _25471 : Type'} (h1' : _25471) (h2' : _25470) (P : type1470 _25470 _25471) (t1 : list _25471) (t2 : list _25470) : term106 _25470 _25471 h1' h2' P t1 t2.
Proof. exact (proj2 (@lem1164269 _25470 _25471 h1' h2' P t1 t2)). Qed.
Lemma lem1164275 {_27428 _27429 : Type'} (m : list _27428) (P : type1470 _27428 _27429) (Q : type1470 _27428 _27429) (t : list _27429) (h1 : term5 _27428 _27429 P Q t) : term113 _27428 _27429 P Q t m.
Proof. exact (@lem1164090 _27428 _27429 P Q t h1 m). Qed.
Lemma lem1164276 {_27428 _27429 : Type'} (P : type1470 _27428 _27429) (Q : type1470 _27428 _27429) (t : list _27429) (m : list _27428) : (term113 _27428 _27429 P Q t m) = ((term1 _27428 _27429 P Q t m) = (term0 _27428 _27429 P Q t m)).
Proof. exact (eq_refl (term113 _27428 _27429 P Q t m)). Qed.
Lemma lem1164281 {_25470 _25471 : Type'} (h1' : _25471) (h2' : _25470) (P : type1470 _25470 _25471) (t1 : list _25471) (t2 : list _25470) : (term114 _25470 _25471 P h1' t1 h2' t2) = (term115 _25470 _25471 h1' h2' P t1 t2).
Proof. exact (proj2 (@lem1164270 _25470 _25471 h1' h2' P t1 t2)). Qed.
Lemma lem1164282 {_27428 _27429 : Type'} (h1' : _27429) (h2' : _27428) (P : type1470 _27428 _27429) (t1 : list _27429) (t2 : list _27428) : (term114 _27428 _27429 P h1' t1 h2' t2) = (term115 _27428 _27429 h1' h2' P t1 t2).
Proof. exact (@lem1164281 _27428 _27429 h1' h2' P t1 t2). Qed.
Lemma lem1164283 {_27428 _27429 : Type'} (h : _27429) (h' : _27428) (P : type1470 _27428 _27429) (Q : type1470 _27428 _27429) (t : list _27429) (t' : list _27428) : (term83 _27428 _27429 P Q h t h' t') = (term116 _27428 _27429 h h' P Q t t').
Proof. exact (@lem1164282 _27428 _27429 h h' (term102 _27428 _27429 P Q) t t'). Qed.
Lemma lem1164287 {A B : Type'} (f : A -> B) (y : A) : (term117 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem1164288 {_27428 _27429 : Type'} (f : type1470 _27428 _27429) (y : _27429) : (term118 _27428 _27429 f y) = (f y).
Proof. exact (@lem1164287 _27429 (_27428 -> Prop) f y). Qed.
Lemma lem1164289 {_27428 _27429 : Type'} (P : type1470 _27428 _27429) (Q : type1470 _27428 _27429) (h : _27429) : (term119 _27428 _27429 P Q h) = (term120 _27428 _27429 P Q h).
Proof. exact (@lem1164288 _27428 _27429 (term102 _27428 _27429 P Q) h). Qed.
Lemma lem1164290 {_27428 _27429 : Type'} (P : type1470 _27428 _27429) (Q : type1470 _27428 _27429) (x : _27429) : (term120 _27428 _27429 P Q x) = (term121 _27428 _27429 P Q x).
Proof. exact (eq_refl (term120 _27428 _27429 P Q x)). Qed.
Lemma lem1164291 {_27428 _27429 : Type'} (P : type1470 _27428 _27429) (Q : type1470 _27428 _27429) : (term122 _27428 _27429 P Q) = (term102 _27428 _27429 P Q).
Proof. exact (fun_ext (fun x : _27429 => @lem1164290 _27428 _27429 P Q x)). Qed.
Lemma lem1164292 {_27429 : Type'} (h : _27429) : h = h.
Proof. exact (eq_refl h). Qed.
Lemma lem1164293 {_27428 _27429 : Type'} (P : type1470 _27428 _27429) (Q : type1470 _27428 _27429) (h : _27429) : (term119 _27428 _27429 P Q h) = (term120 _27428 _27429 P Q h).
Proof. exact (MK_COMB (@lem1164291 _27428 _27429 P Q) (@lem1164292 _27429 h)). Qed.
Lemma lem1164294 {_27428 : Type'} : (@eq (_27428 -> Prop)) = (@eq (_27428 -> Prop)).
Proof. exact (eq_refl (@eq (_27428 -> Prop))). Qed.
Lemma lem1164295 {_27428 _27429 : Type'} (P : type1470 _27428 _27429) (Q : type1470 _27428 _27429) (h : _27429) : (term123 _27428 _27429 P Q h) = (term124 _27428 _27429 P Q h).
Proof. exact (MK_COMB (@lem1164294 _27428) (@lem1164293 _27428 _27429 P Q h)). Qed.
Lemma lem1164296 {_27428 _27429 : Type'} (P : type1470 _27428 _27429) (Q : type1470 _27428 _27429) (h : _27429) : (term120 _27428 _27429 P Q h) = (term121 _27428 _27429 P Q h).
Proof. exact (eq_refl (term120 _27428 _27429 P Q h)). Qed.
Lemma lem1164297 {_27428 _27429 : Type'} (P : type1470 _27428 _27429) (Q : type1470 _27428 _27429) (h : _27429) : ((term119 _27428 _27429 P Q h) = (term120 _27428 _27429 P Q h)) = ((term120 _27428 _27429 P Q h) = (term121 _27428 _27429 P Q h)).
Proof. exact (MK_COMB (@lem1164295 _27428 _27429 P Q h) (@lem1164296 _27428 _27429 P Q h)). Qed.
Lemma lem1164298 {_27428 _27429 : Type'} (P : type1470 _27428 _27429) (Q : type1470 _27428 _27429) (h : _27429) : (term120 _27428 _27429 P Q h) = (term121 _27428 _27429 P Q h).
Proof. exact (EQ_MP (@lem1164297 _27428 _27429 P Q h) (@lem1164289 _27428 _27429 P Q h)). Qed.
Lemma lem1164301 {_27428 : Type'} (h' : _27428) : h' = h'.
Proof. exact (eq_refl h'). Qed.
Lemma lem1164302 {_27428 _27429 : Type'} (P : type1470 _27428 _27429) (Q : type1470 _27428 _27429) (h : _27429) (h' : _27428) : (term125 _27428 _27429 P Q h h') = (term126 _27428 _27429 P Q h h').
Proof. exact (MK_COMB (@lem1164298 _27428 _27429 P Q h) (@lem1164301 _27428 h')). Qed.
Lemma lem1164304 {A B : Type'} (f : A -> B) (y : A) : (term117 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem1164305 {_27428 : Type'} (f : _27428 -> Prop) (y : _27428) : (term127 _27428 f y) = (f y).
Proof. exact (@lem1164304 _27428 Prop f y). Qed.
Lemma lem1164306 {_27428 _27429 : Type'} (P : type1470 _27428 _27429) (Q : type1470 _27428 _27429) (h : _27429) (h' : _27428) : (term128 _27428 _27429 P Q h h') = (term126 _27428 _27429 P Q h h').
Proof. exact (@lem1164305 _27428 (term121 _27428 _27429 P Q h) h'). Qed.
Lemma lem1164307 {_27428 _27429 : Type'} (P : type1470 _27428 _27429) (Q : type1470 _27428 _27429) (h : _27429) (y : _27428) : (term126 _27428 _27429 P Q h y) = (term129 _27428 _27429 P Q h y).
Proof. exact (eq_refl (term126 _27428 _27429 P Q h y)). Qed.
Lemma lem1164308 {_27428 _27429 : Type'} (P : type1470 _27428 _27429) (Q : type1470 _27428 _27429) (h : _27429) : (term130 _27428 _27429 P Q h) = (term121 _27428 _27429 P Q h).
Proof. exact (fun_ext (fun y : _27428 => @lem1164307 _27428 _27429 P Q h y)). Qed.
Lemma lem1164309 {_27428 : Type'} (h' : _27428) : h' = h'.
Proof. exact (eq_refl h'). Qed.
Lemma lem1164310 {_27428 _27429 : Type'} (P : type1470 _27428 _27429) (Q : type1470 _27428 _27429) (h : _27429) (h' : _27428) : (term128 _27428 _27429 P Q h h') = (term126 _27428 _27429 P Q h h').
Proof. exact (MK_COMB (@lem1164308 _27428 _27429 P Q h) (@lem1164309 _27428 h')). Qed.
Lemma lem1164311 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1164312 {_27428 _27429 : Type'} (P : type1470 _27428 _27429) (Q : type1470 _27428 _27429) (h : _27429) (h' : _27428) : (term131 _27428 _27429 P Q h h') = (term132 _27428 _27429 P Q h h').
Proof. exact (MK_COMB (@lem1164311) (@lem1164310 _27428 _27429 P Q h h')). Qed.
Lemma lem1164313 {_27428 _27429 : Type'} (P : type1470 _27428 _27429) (Q : type1470 _27428 _27429) (h : _27429) (h' : _27428) : (term126 _27428 _27429 P Q h h') = (term129 _27428 _27429 P Q h h').
Proof. exact (eq_refl (term126 _27428 _27429 P Q h h')). Qed.
Lemma lem1164314 {_27428 _27429 : Type'} (P : type1470 _27428 _27429) (Q : type1470 _27428 _27429) (h : _27429) (h' : _27428) : ((term128 _27428 _27429 P Q h h') = (term126 _27428 _27429 P Q h h')) = ((term126 _27428 _27429 P Q h h') = (term129 _27428 _27429 P Q h h')).
Proof. exact (MK_COMB (@lem1164312 _27428 _27429 P Q h h') (@lem1164313 _27428 _27429 P Q h h')). Qed.
Lemma lem1164315 {_27428 _27429 : Type'} (P : type1470 _27428 _27429) (Q : type1470 _27428 _27429) (h : _27429) (h' : _27428) : (term126 _27428 _27429 P Q h h') = (term129 _27428 _27429 P Q h h').
Proof. exact (EQ_MP (@lem1164314 _27428 _27429 P Q h h') (@lem1164306 _27428 _27429 P Q h h')). Qed.
Lemma lem1164318 {_27428 _27429 : Type'} (P : type1470 _27428 _27429) (Q : type1470 _27428 _27429) (h : _27429) (h' : _27428) : (term125 _27428 _27429 P Q h h') = (term129 _27428 _27429 P Q h h').
Proof. exact (TRANS (@lem1164302 _27428 _27429 P Q h h') (@lem1164315 _27428 _27429 P Q h h')). Qed.
Lemma lem1164319 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1164320 {_27428 _27429 : Type'} (P : type1470 _27428 _27429) (Q : type1470 _27428 _27429) (h : _27429) (h' : _27428) : (term133 _27428 _27429 P Q h h') = (term134 _27428 _27429 P Q h h').
Proof. exact (MK_COMB (@lem1164319) (@lem1164318 _27428 _27429 P Q h h')). Qed.
Lemma lem1164322 {_27428 _27429 : Type'} (m : list _27428) (P : type1470 _27428 _27429) (Q : type1470 _27428 _27429) (t : list _27429) (h1 : term5 _27428 _27429 P Q t) : (term1 _27428 _27429 P Q t m) = (term0 _27428 _27429 P Q t m).
Proof. exact (EQ_MP (@lem1164276 _27428 _27429 P Q t m) (@lem1164275 _27428 _27429 m P Q t h1)). Qed.
Lemma lem1164323 {_27428 _27429 : Type'} (m : list _27428) (P : type1470 _27428 _27429) (Q : type1470 _27428 _27429) (t : list _27429) (h1 : term5 _27428 _27429 P Q t) : (term1 _27428 _27429 P Q t m) = (term0 _27428 _27429 P Q t m).
Proof. exact (@lem1164322 _27428 _27429 m P Q t h1). Qed.
Lemma lem1164324 {_27428 _27429 : Type'} (t' : list _27428) (P : type1470 _27428 _27429) (Q : type1470 _27428 _27429) (t : list _27429) (h1 : term5 _27428 _27429 P Q t) : (term1 _27428 _27429 P Q t t') = (term0 _27428 _27429 P Q t t').
Proof. exact (@lem1164323 _27428 _27429 t' P Q t h1). Qed.
Lemma lem1164327 {_27428 _27429 : Type'} (h : _27429) (h' : _27428) (t' : list _27428) (P : type1470 _27428 _27429) (Q : type1470 _27428 _27429) (t : list _27429) (h1 : term5 _27428 _27429 P Q t) : (term116 _27428 _27429 h h' P Q t t') = (term135 _27428 _27429 h h' P Q t t').
Proof. exact (MK_COMB (@lem1164320 _27428 _27429 P Q h h') (@lem1164324 _27428 _27429 t' P Q t h1)). Qed.
Lemma lem1164330 {_27428 _27429 : Type'} (h : _27429) (h' : _27428) (t' : list _27428) (P : type1470 _27428 _27429) (Q : type1470 _27428 _27429) (t : list _27429) (h1 : term5 _27428 _27429 P Q t) : (term83 _27428 _27429 P Q h t h' t') = (term135 _27428 _27429 h h' P Q t t').
Proof. exact (TRANS (@lem1164283 _27428 _27429 h h' P Q t t') (@lem1164327 _27428 _27429 h h' t' P Q t h1)). Qed.
Lemma lem1164331 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1164332 {_27428 _27429 : Type'} (h : _27429) (h' : _27428) (t' : list _27428) (P : type1470 _27428 _27429) (Q : type1470 _27428 _27429) (t : list _27429) (h1 : term5 _27428 _27429 P Q t) : (term136 _27428 _27429 P Q h t h' t') = (term137 _27428 _27429 h h' P Q t t').
Proof. exact (MK_COMB (@lem1164331) (@lem1164330 _27428 _27429 h h' t' P Q t h1)). Qed.
Lemma lem1164336 {_25470 _25471 : Type'} (h1' : _25471) (h2' : _25470) (P : type1470 _25470 _25471) (t1 : list _25471) (t2 : list _25470) : (term114 _25470 _25471 P h1' t1 h2' t2) = (term115 _25470 _25471 h1' h2' P t1 t2).
Proof. exact (proj2 (@lem1164270 _25470 _25471 h1' h2' P t1 t2)). Qed.
Lemma lem1164337 {_27428 _27429 : Type'} (h1' : _27429) (h2' : _27428) (P : type1470 _27428 _27429) (t1 : list _27429) (t2 : list _27428) : (term114 _27428 _27429 P h1' t1 h2' t2) = (term115 _27428 _27429 h1' h2' P t1 t2).
Proof. exact (@lem1164336 _27428 _27429 h1' h2' P t1 t2). Qed.
Lemma lem1164338 {_27428 _27429 : Type'} (h : _27429) (h' : _27428) (P : type1470 _27428 _27429) (t : list _27429) (t' : list _27428) : (term114 _27428 _27429 P h t h' t') = (term115 _27428 _27429 h h' P t t').
Proof. exact (@lem1164337 _27428 _27429 h h' P t t'). Qed.
Lemma lem1164341 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1164342 {_27428 _27429 : Type'} (h : _27429) (h' : _27428) (P : type1470 _27428 _27429) (t : list _27429) (t' : list _27428) : (term138 _27428 _27429 P h t h' t') = (term139 _27428 _27429 h h' P t t').
Proof. exact (MK_COMB (@lem1164341) (@lem1164338 _27428 _27429 h h' P t t')). Qed.
Lemma lem1164344 {_25470 _25471 : Type'} (h1' : _25471) (h2' : _25470) (P : type1470 _25470 _25471) (t1 : list _25471) (t2 : list _25470) : (term114 _25470 _25471 P h1' t1 h2' t2) = (term115 _25470 _25471 h1' h2' P t1 t2).
Proof. exact (proj2 (@lem1164270 _25470 _25471 h1' h2' P t1 t2)). Qed.
Lemma lem1164345 {_27428 _27429 : Type'} (h1' : _27429) (h2' : _27428) (P : type1470 _27428 _27429) (t1 : list _27429) (t2 : list _27428) : (term114 _27428 _27429 P h1' t1 h2' t2) = (term115 _27428 _27429 h1' h2' P t1 t2).
Proof. exact (@lem1164344 _27428 _27429 h1' h2' P t1 t2). Qed.
Lemma lem1164346 {_27428 _27429 : Type'} (h : _27429) (h' : _27428) (Q : type1470 _27428 _27429) (t : list _27429) (t' : list _27428) : (term114 _27428 _27429 Q h t h' t') = (term115 _27428 _27429 h h' Q t t').
Proof. exact (@lem1164345 _27428 _27429 h h' Q t t'). Qed.
Lemma lem1164349 {_27428 _27429 : Type'} (P : type1470 _27428 _27429) (h : _27429) (h' : _27428) (Q : type1470 _27428 _27429) (t : list _27429) (t' : list _27428) : (term84 _27428 _27429 P Q h t h' t') = (term140 _27428 _27429 P h h' Q t t').
Proof. exact (MK_COMB (@lem1164342 _27428 _27429 h h' P t t') (@lem1164346 _27428 _27429 h h' Q t t')). Qed.
Lemma lem1164352 {_27428 _27429 : Type'} (h : _27429) (h' : _27428) (t' : list _27428) (P : type1470 _27428 _27429) (Q : type1470 _27428 _27429) (t : list _27429) (h1 : term5 _27428 _27429 P Q t) : ((term83 _27428 _27429 P Q h t h' t') = (term84 _27428 _27429 P Q h t h' t')) = ((term135 _27428 _27429 h h' P Q t t') = (term140 _27428 _27429 P h h' Q t t')).
Proof. exact (MK_COMB (@lem1164332 _27428 _27429 h h' t' P Q t h1) (@lem1164349 _27428 _27429 P h h' Q t t')). Qed.
Lemma lem1164355 {_27428 _27429 : Type'} (h : _27429) (h' : _27428) (t' : list _27428) (P : type1470 _27428 _27429) (Q : type1470 _27428 _27429) (t : list _27429) (h1 : term5 _27428 _27429 P Q t) : ((term135 _27428 _27429 h h' P Q t t') = (term140 _27428 _27429 P h h' Q t t')) = ((term83 _27428 _27429 P Q h t h' t') = (term84 _27428 _27429 P Q h t h' t')).
Proof. exact (SYM (@lem1164352 _27428 _27429 h h' t' P Q t h1)). Qed.
Lemma lem1164359 (p : Prop) (q : Prop) (r : Prop) : (term141 p q r) = (term142 p q r).
Proof. exact (EQ_MP (@lem586 p q r) (@lem585 p q r)). Qed.
Lemma lem1164360 {_27428 _27429 : Type'} (h : _27429) (h' : _27428) (P : type1470 _27428 _27429) (Q : type1470 _27428 _27429) (t : list _27429) (t' : list _27428) : (term135 _27428 _27429 h h' P Q t t') = (term143 _27428 _27429 h h' P Q t t').
Proof. exact (@lem1164359 (P h h') (Q h h') (term0 _27428 _27429 P Q t t')). Qed.
Lemma lem1164392 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1164393 {_27428 _27429 : Type'} (h : _27429) (h' : _27428) (P : type1470 _27428 _27429) (Q : type1470 _27428 _27429) (t : list _27429) (t' : list _27428) : (term137 _27428 _27429 h h' P Q t t') = (term144 _27428 _27429 h h' P Q t t').
Proof. exact (MK_COMB (@lem1164392) (@lem1164360 _27428 _27429 h h' P Q t t')). Qed.
Lemma lem1164395 (p : Prop) (q : Prop) (r : Prop) : (term141 p q r) = (term142 p q r).
Proof. exact (EQ_MP (@lem586 p q r) (@lem585 p q r)). Qed.
Lemma lem1164396 {_27428 _27429 : Type'} (P : type1470 _27428 _27429) (h : _27429) (h' : _27428) (Q : type1470 _27428 _27429) (t : list _27429) (t' : list _27428) : (term140 _27428 _27429 P h h' Q t t') = (term145 _27428 _27429 P h h' Q t t').
Proof. exact (@lem1164395 (P h h') (@ALL2 _27429 _27428 P t t') (term115 _27428 _27429 h h' Q t t')). Qed.
Lemma lem1164412 (q : Prop) (p : Prop) (r : Prop) : (term142 p q r) = (term142 q p r).
Proof. exact (EQ_MP (@lem617 q p r) (@lem616 p q r)). Qed.
Lemma lem1164413 {_27428 _27429 : Type'} (h : _27429) (h' : _27428) (P : type1470 _27428 _27429) (Q : type1470 _27428 _27429) (t : list _27429) (t' : list _27428) : (term146 _27428 _27429 P h h' Q t t') = (term147 _27428 _27429 h h' P Q t t').
Proof. exact (@lem1164412 (Q h h') (@ALL2 _27429 _27428 P t t') (@ALL2 _27429 _27428 Q t t')). Qed.
Lemma lem1164433 {_27428 _27429 : Type'} (P : type1470 _27428 _27429) (h : _27429) (h' : _27428) : (term148 _27428 _27429 P h h') = (term148 _27428 _27429 P h h').
Proof. exact (eq_refl (term148 _27428 _27429 P h h')). Qed.
Lemma lem1164434 {_27428 _27429 : Type'} (h : _27429) (h' : _27428) (P : type1470 _27428 _27429) (Q : type1470 _27428 _27429) (t : list _27429) (t' : list _27428) : (term145 _27428 _27429 P h h' Q t t') = (term143 _27428 _27429 h h' P Q t t').
Proof. exact (MK_COMB (@lem1164433 _27428 _27429 P h h') (@lem1164413 _27428 _27429 h h' P Q t t')). Qed.
Lemma lem1164447 {_27428 _27429 : Type'} (h : _27429) (h' : _27428) (P : type1470 _27428 _27429) (Q : type1470 _27428 _27429) (t : list _27429) (t' : list _27428) : (term140 _27428 _27429 P h h' Q t t') = (term143 _27428 _27429 h h' P Q t t').
Proof. exact (TRANS (@lem1164396 _27428 _27429 P h h' Q t t') (@lem1164434 _27428 _27429 h h' P Q t t')). Qed.
Lemma lem1164448 {_27428 _27429 : Type'} (h : _27429) (h' : _27428) (P : type1470 _27428 _27429) (Q : type1470 _27428 _27429) (t : list _27429) (t' : list _27428) : ((term135 _27428 _27429 h h' P Q t t') = (term140 _27428 _27429 P h h' Q t t')) = ((term143 _27428 _27429 h h' P Q t t') = (term143 _27428 _27429 h h' P Q t t')).
Proof. exact (MK_COMB (@lem1164393 _27428 _27429 h h' P Q t t') (@lem1164447 _27428 _27429 h h' P Q t t')). Qed.
Lemma lem1164450 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1164451 (x : Prop) : (x = x) = True.
Proof. exact (@lem1164450 Prop x). Qed.
Lemma lem1164452 {_27428 _27429 : Type'} (h : _27429) (h' : _27428) (P : type1470 _27428 _27429) (Q : type1470 _27428 _27429) (t : list _27429) (t' : list _27428) : ((term143 _27428 _27429 h h' P Q t t') = (term143 _27428 _27429 h h' P Q t t')) = True.
Proof. exact (@lem1164451 (term143 _27428 _27429 h h' P Q t t')). Qed.
Lemma lem1164453 {_27428 _27429 : Type'} (P : type1470 _27428 _27429) (h : _27429) (h' : _27428) (Q : type1470 _27428 _27429) (t : list _27429) (t' : list _27428) : ((term135 _27428 _27429 h h' P Q t t') = (term140 _27428 _27429 P h h' Q t t')) = True.
Proof. exact (TRANS (@lem1164448 _27428 _27429 h h' P Q t t') (@lem1164452 _27428 _27429 h h' P Q t t')). Qed.
Lemma lem1164454 {_27428 _27429 : Type'} (P : type1470 _27428 _27429) (h : _27429) (h' : _27428) (Q : type1470 _27428 _27429) (t : list _27429) (t' : list _27428) : True = ((term135 _27428 _27429 h h' P Q t t') = (term140 _27428 _27429 P h h' Q t t')).
Proof. exact (SYM (@lem1164453 _27428 _27429 P h h' Q t t')). Qed.
Lemma lem1164455 {_27428 _27429 : Type'} (P : type1470 _27428 _27429) (h : _27429) (h' : _27428) (Q : type1470 _27428 _27429) (t : list _27429) (t' : list _27428) : (term135 _27428 _27429 h h' P Q t t') = (term140 _27428 _27429 P h h' Q t t').
Proof. exact (EQ_MP (@lem1164454 _27428 _27429 P h h' Q t t') (@lem0)). Qed.
Lemma lem1164456 {_27428 _27429 : Type'} (h : _27429) (h' : _27428) (t' : list _27428) (P : type1470 _27428 _27429) (Q : type1470 _27428 _27429) (t : list _27429) (h1 : term5 _27428 _27429 P Q t) : (term83 _27428 _27429 P Q h t h' t') = (term84 _27428 _27429 P Q h t h' t').
Proof. exact (EQ_MP (@lem1164355 _27428 _27429 h h' t' P Q t h1) (@lem1164455 _27428 _27429 P h h' Q t t')). Qed.
Lemma lem1164457 {_27428 _27429 : Type'} (h : _27429) (h' : _27428) (t' : list _27428) (P : type1470 _27428 _27429) (Q : type1470 _27428 _27429) (t : list _27429) (h1 : term5 _27428 _27429 P Q t) : term86 _27428 _27429 P Q h t h' t'.
Proof. exact (fun h0 : (term78 _27428 _27429 P Q h t t') = (term79 _27428 _27429 P Q h t t') => @lem1164456 _27428 _27429 h h' t' P Q t h1). Qed.
Lemma lem1164462 {_27428 _27429 : Type'} (h : _27429) (h' : _27428) (P : type1470 _27428 _27429) (Q : type1470 _27428 _27429) (t : list _27429) (h1 : term5 _27428 _27429 P Q t) : term90 _27428 _27429 P Q h t h'.
Proof. exact (fun t' : list _27428 => @lem1164457 _27428 _27429 h h' t' P Q t h1). Qed.
Lemma lem1164467 {_27428 _27429 : Type'} (h : _27429) (P : type1470 _27428 _27429) (Q : type1470 _27428 _27429) (t : list _27429) (h1 : term5 _27428 _27429 P Q t) : term94 _27428 _27429 P Q h t.
Proof. exact (fun h' : _27428 => @lem1164462 _27428 _27429 h h' P Q t h1). Qed.
Lemma lem1164468 {_27428 _27429 : Type'} (h : _27429) (P : type1470 _27428 _27429) (Q : type1470 _27428 _27429) (t : list _27429) (h1 : term5 _27428 _27429 P Q t) : term96 _27428 _27429 P Q h t.
Proof. exact (conj (@lem1164268 _27428 _27429 P Q h t) (@lem1164467 _27428 _27429 h P Q t h1)). Qed.
Lemma lem1164469 {_27428 _27429 : Type'} (h : _27429) (P : type1470 _27428 _27429) (Q : type1470 _27428 _27429) (t : list _27429) (h1 : term5 _27428 _27429 P Q t) : term20 _27428 _27429 P Q h t.
Proof. exact (@lem1164145 _27428 _27429 P Q h t (@lem1164468 _27428 _27429 h P Q t h1)). Qed.
Lemma lem1164470 {_27428 _27429 : Type'} (P : type1470 _27428 _27429) (Q : type1470 _27428 _27429) (h : _27428) (t : list _27428) : term54 _27428 _27429 P Q h t.
Proof. exact (fun h0 : (term46 _27428 _27429 P Q t) = (term47 _27428 _27429 P Q t) => @lem1164224 _27428 _27429 P Q h t). Qed.
Lemma lem1164475 {_27428 _27429 : Type'} (P : type1470 _27428 _27429) (Q : type1470 _27428 _27429) (h : _27428) : term58 _27428 _27429 P Q h.
Proof. exact (fun t : list _27428 => @lem1164470 _27428 _27429 P Q h t). Qed.
Lemma lem1164480 {_27428 _27429 : Type'} (P : type1470 _27428 _27429) (Q : type1470 _27428 _27429) : term62 _27428 _27429 P Q.
Proof. exact (fun h : _27428 => @lem1164475 _27428 _27429 P Q h). Qed.
Lemma lem1164481 {_27428 _27429 : Type'} (P : type1470 _27428 _27429) (Q : type1470 _27428 _27429) : term64 _27428 _27429 P Q.
Proof. exact (conj (@lem1164183 _27428 _27429 P Q) (@lem1164480 _27428 _27429 P Q)). Qed.
Lemma lem1164482 {_27428 _27429 : Type'} (P : type1470 _27428 _27429) (Q : type1470 _27428 _27429) : term13 _27428 _27429 P Q.
Proof. exact (@lem1164117 _27428 _27429 P Q (@lem1164481 _27428 _27429 P Q)). Qed.
Lemma lem1164483 {_27428 _27429 : Type'} (P : type1470 _27428 _27429) (Q : type1470 _27428 _27429) (h : _27429) (t : list _27429) : term22 _27428 _27429 P Q h t.
Proof. exact (fun h0 : term5 _27428 _27429 P Q t => @lem1164469 _27428 _27429 h P Q t h0). Qed.
Lemma lem1164488 {_27428 _27429 : Type'} (P : type1470 _27428 _27429) (Q : type1470 _27428 _27429) (h : _27429) : term26 _27428 _27429 P Q h.
Proof. exact (fun t : list _27429 => @lem1164483 _27428 _27429 P Q h t). Qed.
Lemma lem1164493 {_27428 _27429 : Type'} (P : type1470 _27428 _27429) (Q : type1470 _27428 _27429) : term30 _27428 _27429 P Q.
Proof. exact (fun h : _27429 => @lem1164488 _27428 _27429 P Q h). Qed.
Lemma lem1164494 {_27428 _27429 : Type'} (P : type1470 _27428 _27429) (Q : type1470 _27428 _27429) : term32 _27428 _27429 P Q.
Proof. exact (conj (@lem1164482 _27428 _27429 P Q) (@lem1164493 _27428 _27429 P Q)). Qed.
Lemma lem1164495 {_27428 _27429 : Type'} (P : type1470 _27428 _27429) (Q : type1470 _27428 _27429) : term9 _27428 _27429 P Q.
Proof. exact (@lem1164089 _27428 _27429 P Q (@lem1164494 _27428 _27429 P Q)). Qed.
Lemma lem1164496 {_27428 _27429 : Type'} (P : type1470 _27428 _27429) (Q : type1470 _27428 _27429) : term8 _27428 _27429 P Q.
Proof. exact (EQ_MP (@lem1164062 _27428 _27429 P Q) (@lem1164495 _27428 _27429 P Q)). Qed.
Lemma lem1164501 {_27428 _27429 : Type'} (P : type1470 _27428 _27429) : term149 _27428 _27429 P.
Proof. exact (fun Q : type1470 _27428 _27429 => @lem1164496 _27428 _27429 P Q). Qed.
Lemma lem1164506 {_27428 _27429 : Type'} : term150 _27428 _27429.
Proof. exact (fun P : type1470 _27428 _27429 => @lem1164501 _27428 _27429 P). Qed.
