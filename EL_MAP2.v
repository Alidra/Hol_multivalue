Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import EL_MAP2_term_abbrevs.
Require Import LT_SUC_spec.
Require Import MAP2_spec.
Require Import thm0_spec.
Require Import thm1094346_spec.
Require Import thm1094347_spec.
Require Import thm1094865_spec.
Require Import thm1094866_spec.
Require Import thm1095388_spec.
Require Import thm1095389_spec.
Require Import thm1097080_spec.
Require Import thm1105741_spec.
Require Import thm1105742_spec.
Require Import thm1105747_spec.
Require Import thm1105748_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1822_spec.
Require Import thm1842_spec.
Require Import thm1844_spec.
Require Import thm1845_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Require Import thm75622_spec.
Require Import thm75623_spec.
Require Import thm89994_spec.
Lemma lem1189024 : term0.
Proof. exact (proj1 (@lem89994)). Qed.
Lemma lem1189026 {A : Type'} (P : type1143 A) : term1 A P.
Proof. exact (EQ_MP (@lem1094347 A P) (@lem1094346 A P)). Qed.
Lemma lem1189027 {_27798 : Type'} (P : type1143 _27798) : term1 _27798 P.
Proof. exact (@lem1189026 _27798 P). Qed.
Lemma lem1189028 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) : term2 _27796 _27797 _27798 f.
Proof. exact (@lem1189027 _27798 (term3 _27796 _27797 _27798 f)). Qed.
Lemma lem1189029 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) : (term4 _27796 _27797 _27798 f) = (term5 _27796 _27797 _27798 f).
Proof. exact (eq_refl (term4 _27796 _27797 _27798 f)). Qed.
Lemma lem1189030 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1189031 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) : (term6 _27796 _27797 _27798 f) = (term7 _27796 _27797 _27798 f).
Proof. exact (MK_COMB (@lem1189030) (@lem1189029 _27796 _27797 _27798 f)). Qed.
Lemma lem1189032 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (t : list _27798) : (term8 _27796 _27797 _27798 f t) = (term9 _27796 _27797 _27798 f t).
Proof. exact (eq_refl (term8 _27796 _27797 _27798 f t)). Qed.
Lemma lem1189033 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1189034 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (t : list _27798) : (term10 _27796 _27797 _27798 f t) = (term11 _27796 _27797 _27798 f t).
Proof. exact (MK_COMB (@lem1189033) (@lem1189032 _27796 _27797 _27798 f t)). Qed.
Lemma lem1189035 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (h : _27798) (t : list _27798) : (term12 _27796 _27797 _27798 f h t) = (term13 _27796 _27797 _27798 f h t).
Proof. exact (eq_refl (term12 _27796 _27797 _27798 f h t)). Qed.
Lemma lem1189036 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (h : _27798) (t : list _27798) : (term14 _27796 _27797 _27798 f h t) = (term15 _27796 _27797 _27798 f h t).
Proof. exact (MK_COMB (@lem1189034 _27796 _27797 _27798 f t) (@lem1189035 _27796 _27797 _27798 f h t)). Qed.
Lemma lem1189037 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (h : _27798) : (term16 _27796 _27797 _27798 f h) = (term17 _27796 _27797 _27798 f h).
Proof. exact (fun_ext (fun t : list _27798 => @lem1189036 _27796 _27797 _27798 f h t)). Qed.
Lemma lem1189038 {_27798 : Type'} : (@all (list _27798)) = (@all (list _27798)).
Proof. exact (eq_refl (@all (list _27798))). Qed.
Lemma lem1189039 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (h : _27798) : (term18 _27796 _27797 _27798 f h) = (term19 _27796 _27797 _27798 f h).
Proof. exact (MK_COMB (@lem1189038 _27798) (@lem1189037 _27796 _27797 _27798 f h)). Qed.
Lemma lem1189040 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) : (term20 _27796 _27797 _27798 f) = (term21 _27796 _27797 _27798 f).
Proof. exact (fun_ext (fun h : _27798 => @lem1189039 _27796 _27797 _27798 f h)). Qed.
Lemma lem1189041 {_27798 : Type'} : (@all _27798) = (@all _27798).
Proof. exact (eq_refl (@all _27798)). Qed.
Lemma lem1189042 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) : (term22 _27796 _27797 _27798 f) = (term23 _27796 _27797 _27798 f).
Proof. exact (MK_COMB (@lem1189041 _27798) (@lem1189040 _27796 _27797 _27798 f)). Qed.
Lemma lem1189043 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) : (term24 _27796 _27797 _27798 f) = (term25 _27796 _27797 _27798 f).
Proof. exact (MK_COMB (@lem1189031 _27796 _27797 _27798 f) (@lem1189042 _27796 _27797 _27798 f)). Qed.
Lemma lem1189044 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1189045 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) : (term26 _27796 _27797 _27798 f) = (term27 _27796 _27797 _27798 f).
Proof. exact (MK_COMB (@lem1189044) (@lem1189043 _27796 _27797 _27798 f)). Qed.
Lemma lem1189046 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (l : list _27798) : (term8 _27796 _27797 _27798 f l) = (term9 _27796 _27797 _27798 f l).
Proof. exact (eq_refl (term8 _27796 _27797 _27798 f l)). Qed.
Lemma lem1189047 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) : (term28 _27796 _27797 _27798 f) = (term3 _27796 _27797 _27798 f).
Proof. exact (fun_ext (fun l : list _27798 => @lem1189046 _27796 _27797 _27798 f l)). Qed.
Lemma lem1189048 {_27798 : Type'} : (@all (list _27798)) = (@all (list _27798)).
Proof. exact (eq_refl (@all (list _27798))). Qed.
Lemma lem1189049 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) : (term29 _27796 _27797 _27798 f) = (term30 _27796 _27797 _27798 f).
Proof. exact (MK_COMB (@lem1189048 _27798) (@lem1189047 _27796 _27797 _27798 f)). Qed.
Lemma lem1189050 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) : (term2 _27796 _27797 _27798 f) = (term31 _27796 _27797 _27798 f).
Proof. exact (MK_COMB (@lem1189045 _27796 _27797 _27798 f) (@lem1189049 _27796 _27797 _27798 f)). Qed.
Lemma lem1189051 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) : term31 _27796 _27797 _27798 f.
Proof. exact (EQ_MP (@lem1189050 _27796 _27797 _27798 f) (@lem1189028 _27796 _27797 _27798 f)). Qed.
Lemma lem1189052 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (t : list _27798) (h1 : term9 _27796 _27797 _27798 f t) : term9 _27796 _27797 _27798 f t.
Proof. exact (h1). Qed.
Lemma lem1189054 {A : Type'} (P : type1143 A) : term1 A P.
Proof. exact (EQ_MP (@lem1094347 A P) (@lem1094346 A P)). Qed.
Lemma lem1189055 {_27797 : Type'} (P : type1143 _27797) : term1 _27797 P.
Proof. exact (@lem1189054 _27797 P). Qed.
Lemma lem1189056 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) : term32 _27796 _27797 _27798 f.
Proof. exact (@lem1189055 _27797 (term33 _27796 _27797 _27798 f)). Qed.
Lemma lem1189057 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) : (term34 _27796 _27797 _27798 f) = (term35 _27796 _27797 _27798 f).
Proof. exact (eq_refl (term34 _27796 _27797 _27798 f)). Qed.
Lemma lem1189058 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1189059 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) : (term36 _27796 _27797 _27798 f) = (term37 _27796 _27797 _27798 f).
Proof. exact (MK_COMB (@lem1189058) (@lem1189057 _27796 _27797 _27798 f)). Qed.
Lemma lem1189060 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (t : list _27797) : (term38 _27796 _27797 _27798 f t) = (term39 _27796 _27797 _27798 f t).
Proof. exact (eq_refl (term38 _27796 _27797 _27798 f t)). Qed.
Lemma lem1189061 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1189062 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (t : list _27797) : (term40 _27796 _27797 _27798 f t) = (term41 _27796 _27797 _27798 f t).
Proof. exact (MK_COMB (@lem1189061) (@lem1189060 _27796 _27797 _27798 f t)). Qed.
Lemma lem1189063 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (h : _27797) (t : list _27797) : (term42 _27796 _27797 _27798 f h t) = (term43 _27796 _27797 _27798 f h t).
Proof. exact (eq_refl (term42 _27796 _27797 _27798 f h t)). Qed.
Lemma lem1189064 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (h : _27797) (t : list _27797) : (term44 _27796 _27797 _27798 f h t) = (term45 _27796 _27797 _27798 f h t).
Proof. exact (MK_COMB (@lem1189062 _27796 _27797 _27798 f t) (@lem1189063 _27796 _27797 _27798 f h t)). Qed.
Lemma lem1189065 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (h : _27797) : (term46 _27796 _27797 _27798 f h) = (term47 _27796 _27797 _27798 f h).
Proof. exact (fun_ext (fun t : list _27797 => @lem1189064 _27796 _27797 _27798 f h t)). Qed.
Lemma lem1189066 {_27797 : Type'} : (@all (list _27797)) = (@all (list _27797)).
Proof. exact (eq_refl (@all (list _27797))). Qed.
Lemma lem1189067 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (h : _27797) : (term48 _27796 _27797 _27798 f h) = (term49 _27796 _27797 _27798 f h).
Proof. exact (MK_COMB (@lem1189066 _27797) (@lem1189065 _27796 _27797 _27798 f h)). Qed.
Lemma lem1189068 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) : (term50 _27796 _27797 _27798 f) = (term51 _27796 _27797 _27798 f).
Proof. exact (fun_ext (fun h : _27797 => @lem1189067 _27796 _27797 _27798 f h)). Qed.
Lemma lem1189069 {_27797 : Type'} : (@all _27797) = (@all _27797).
Proof. exact (eq_refl (@all _27797)). Qed.
Lemma lem1189070 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) : (term52 _27796 _27797 _27798 f) = (term53 _27796 _27797 _27798 f).
Proof. exact (MK_COMB (@lem1189069 _27797) (@lem1189068 _27796 _27797 _27798 f)). Qed.
Lemma lem1189071 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) : (term54 _27796 _27797 _27798 f) = (term55 _27796 _27797 _27798 f).
Proof. exact (MK_COMB (@lem1189059 _27796 _27797 _27798 f) (@lem1189070 _27796 _27797 _27798 f)). Qed.
Lemma lem1189072 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1189073 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) : (term56 _27796 _27797 _27798 f) = (term57 _27796 _27797 _27798 f).
Proof. exact (MK_COMB (@lem1189072) (@lem1189071 _27796 _27797 _27798 f)). Qed.
Lemma lem1189074 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (m : list _27797) : (term38 _27796 _27797 _27798 f m) = (term39 _27796 _27797 _27798 f m).
Proof. exact (eq_refl (term38 _27796 _27797 _27798 f m)). Qed.
Lemma lem1189075 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) : (term58 _27796 _27797 _27798 f) = (term33 _27796 _27797 _27798 f).
Proof. exact (fun_ext (fun m : list _27797 => @lem1189074 _27796 _27797 _27798 f m)). Qed.
Lemma lem1189076 {_27797 : Type'} : (@all (list _27797)) = (@all (list _27797)).
Proof. exact (eq_refl (@all (list _27797))). Qed.
Lemma lem1189077 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) : (term59 _27796 _27797 _27798 f) = (term5 _27796 _27797 _27798 f).
Proof. exact (MK_COMB (@lem1189076 _27797) (@lem1189075 _27796 _27797 _27798 f)). Qed.
Lemma lem1189078 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) : (term32 _27796 _27797 _27798 f) = (term60 _27796 _27797 _27798 f).
Proof. exact (MK_COMB (@lem1189073 _27796 _27797 _27798 f) (@lem1189077 _27796 _27797 _27798 f)). Qed.
Lemma lem1189079 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) : term60 _27796 _27797 _27798 f.
Proof. exact (EQ_MP (@lem1189078 _27796 _27797 _27798 f) (@lem1189056 _27796 _27797 _27798 f)). Qed.
Lemma lem1189082 {A : Type'} (P : type1143 A) : term1 A P.
Proof. exact (EQ_MP (@lem1094347 A P) (@lem1094346 A P)). Qed.
Lemma lem1189083 {_27797 : Type'} (P : type1143 _27797) : term1 _27797 P.
Proof. exact (@lem1189082 _27797 P). Qed.
Lemma lem1189084 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (h : _27798) (t : list _27798) : term61 _27796 _27797 _27798 f h t.
Proof. exact (@lem1189083 _27797 (term62 _27796 _27797 _27798 f h t)). Qed.
Lemma lem1189085 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (h : _27798) (t : list _27798) : (term63 _27796 _27797 _27798 f h t) = (term64 _27796 _27797 _27798 f h t).
Proof. exact (eq_refl (term63 _27796 _27797 _27798 f h t)). Qed.
Lemma lem1189086 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1189087 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (h : _27798) (t : list _27798) : (term65 _27796 _27797 _27798 f h t) = (term66 _27796 _27797 _27798 f h t).
Proof. exact (MK_COMB (@lem1189086) (@lem1189085 _27796 _27797 _27798 f h t)). Qed.
Lemma lem1189088 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (h : _27798) (t : list _27798) (t' : list _27797) : (term67 _27796 _27797 _27798 f h t t') = (term68 _27796 _27797 _27798 f h t t').
Proof. exact (eq_refl (term67 _27796 _27797 _27798 f h t t')). Qed.
Lemma lem1189089 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1189090 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (h : _27798) (t : list _27798) (t' : list _27797) : (term69 _27796 _27797 _27798 f h t t') = (term70 _27796 _27797 _27798 f h t t').
Proof. exact (MK_COMB (@lem1189089) (@lem1189088 _27796 _27797 _27798 f h t t')). Qed.
Lemma lem1189091 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (h : _27798) (t : list _27798) (h' : _27797) (t' : list _27797) : (term71 _27796 _27797 _27798 f h t h' t') = (term72 _27796 _27797 _27798 f h t h' t').
Proof. exact (eq_refl (term71 _27796 _27797 _27798 f h t h' t')). Qed.
Lemma lem1189092 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (h : _27798) (t : list _27798) (h' : _27797) (t' : list _27797) : (term73 _27796 _27797 _27798 f h t h' t') = (term74 _27796 _27797 _27798 f h t h' t').
Proof. exact (MK_COMB (@lem1189090 _27796 _27797 _27798 f h t t') (@lem1189091 _27796 _27797 _27798 f h t h' t')). Qed.
Lemma lem1189093 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (h : _27798) (t : list _27798) (h' : _27797) : (term75 _27796 _27797 _27798 f h t h') = (term76 _27796 _27797 _27798 f h t h').
Proof. exact (fun_ext (fun t' : list _27797 => @lem1189092 _27796 _27797 _27798 f h t h' t')). Qed.
Lemma lem1189094 {_27797 : Type'} : (@all (list _27797)) = (@all (list _27797)).
Proof. exact (eq_refl (@all (list _27797))). Qed.
Lemma lem1189095 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (h : _27798) (t : list _27798) (h' : _27797) : (term77 _27796 _27797 _27798 f h t h') = (term78 _27796 _27797 _27798 f h t h').
Proof. exact (MK_COMB (@lem1189094 _27797) (@lem1189093 _27796 _27797 _27798 f h t h')). Qed.
Lemma lem1189096 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (h : _27798) (t : list _27798) : (term79 _27796 _27797 _27798 f h t) = (term80 _27796 _27797 _27798 f h t).
Proof. exact (fun_ext (fun h' : _27797 => @lem1189095 _27796 _27797 _27798 f h t h')). Qed.
Lemma lem1189097 {_27797 : Type'} : (@all _27797) = (@all _27797).
Proof. exact (eq_refl (@all _27797)). Qed.
Lemma lem1189098 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (h : _27798) (t : list _27798) : (term81 _27796 _27797 _27798 f h t) = (term82 _27796 _27797 _27798 f h t).
Proof. exact (MK_COMB (@lem1189097 _27797) (@lem1189096 _27796 _27797 _27798 f h t)). Qed.
Lemma lem1189099 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (h : _27798) (t : list _27798) : (term83 _27796 _27797 _27798 f h t) = (term84 _27796 _27797 _27798 f h t).
Proof. exact (MK_COMB (@lem1189087 _27796 _27797 _27798 f h t) (@lem1189098 _27796 _27797 _27798 f h t)). Qed.
Lemma lem1189100 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1189101 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (h : _27798) (t : list _27798) : (term85 _27796 _27797 _27798 f h t) = (term86 _27796 _27797 _27798 f h t).
Proof. exact (MK_COMB (@lem1189100) (@lem1189099 _27796 _27797 _27798 f h t)). Qed.
Lemma lem1189102 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (h : _27798) (t : list _27798) (m : list _27797) : (term67 _27796 _27797 _27798 f h t m) = (term68 _27796 _27797 _27798 f h t m).
Proof. exact (eq_refl (term67 _27796 _27797 _27798 f h t m)). Qed.
Lemma lem1189103 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (h : _27798) (t : list _27798) : (term87 _27796 _27797 _27798 f h t) = (term62 _27796 _27797 _27798 f h t).
Proof. exact (fun_ext (fun m : list _27797 => @lem1189102 _27796 _27797 _27798 f h t m)). Qed.
Lemma lem1189104 {_27797 : Type'} : (@all (list _27797)) = (@all (list _27797)).
Proof. exact (eq_refl (@all (list _27797))). Qed.
Lemma lem1189105 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (h : _27798) (t : list _27798) : (term88 _27796 _27797 _27798 f h t) = (term13 _27796 _27797 _27798 f h t).
Proof. exact (MK_COMB (@lem1189104 _27797) (@lem1189103 _27796 _27797 _27798 f h t)). Qed.
Lemma lem1189106 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (h : _27798) (t : list _27798) : (term61 _27796 _27797 _27798 f h t) = (term89 _27796 _27797 _27798 f h t).
Proof. exact (MK_COMB (@lem1189101 _27796 _27797 _27798 f h t) (@lem1189105 _27796 _27797 _27798 f h t)). Qed.
Lemma lem1189107 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (h : _27798) (t : list _27798) : term89 _27796 _27797 _27798 f h t.
Proof. exact (EQ_MP (@lem1189106 _27796 _27797 _27798 f h t) (@lem1189084 _27796 _27797 _27798 f h t)). Qed.
Lemma lem1189109 (m : nat) : term90 m.
Proof. exact (@lem1189024 m). Qed.
Lemma lem1189110 (m : nat) : (term90 m) = ((term91 m) = False).
Proof. exact (eq_refl (term90 m)). Qed.
Lemma lem1189127 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term92 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem1189128 (p : Prop) (q : Prop) (p' : Prop) : term93 p q p'.
Proof. exact (fun q' : Prop => @lem1189127 p q p' q'). Qed.
Lemma lem1189129 (p : Prop) (q : Prop) : term94 p q.
Proof. exact (fun p' : Prop => @lem1189128 p q p'). Qed.
Lemma lem1189130 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (k : nat) : term95 _27796 _27797 _27798 f k.
Proof. exact (@lem1189129 (term96 _27797 _27798 k) ((term97 _27796 _27797 _27798 k f) = (term98 _27796 _27797 _27798 f k))). Qed.
Lemma lem1189131 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (k : nat) (p' : Prop) : term99 _27796 _27797 _27798 f k p'.
Proof. exact (@lem1189130 _27796 _27797 _27798 f k p'). Qed.
Lemma lem1189132 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (k : nat) (p' : Prop) : (term99 _27796 _27797 _27798 f k p') = (term100 _27796 _27797 _27798 f k p').
Proof. exact (eq_refl (term99 _27796 _27797 _27798 f k p')). Qed.
Lemma lem1189133 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (k : nat) (p' : Prop) : term100 _27796 _27797 _27798 f k p'.
Proof. exact (EQ_MP (@lem1189132 _27796 _27797 _27798 f k p') (@lem1189131 _27796 _27797 _27798 f k p')). Qed.
Lemma lem1189134 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (k : nat) (p' : Prop) (q' : Prop) : term101 _27796 _27797 _27798 f k p' q'.
Proof. exact (@lem1189133 _27796 _27797 _27798 f k p' q'). Qed.
Lemma lem1189135 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (k : nat) (p' : Prop) (q' : Prop) : (term101 _27796 _27797 _27798 f k p' q') = (term102 _27796 _27797 _27798 f k p' q').
Proof. exact (eq_refl (term101 _27796 _27797 _27798 f k p' q')). Qed.
Lemma lem1189136 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (k : nat) (p' : Prop) (q' : Prop) : term102 _27796 _27797 _27798 f k p' q'.
Proof. exact (EQ_MP (@lem1189135 _27796 _27797 _27798 f k p' q') (@lem1189134 _27796 _27797 _27798 f k p' q')). Qed.
Lemma lem1189140 {A : Type'} : (@List.length A (@nil A)) = (NUMERAL 0).
Proof. exact (proj1 (@lem1097080 A)). Qed.
Lemma lem1189141 {_27798 : Type'} : (@List.length _27798 (@nil _27798)) = (NUMERAL 0).
Proof. exact (@lem1189140 _27798). Qed.
Lemma lem1189142 (k : nat) : (Peano.lt k) = (Peano.lt k).
Proof. exact (eq_refl (Peano.lt k)). Qed.
Lemma lem1189143 {_27798 : Type'} (k : nat) : (term103 _27798 k) = (term91 k).
Proof. exact (MK_COMB (@lem1189142 k) (@lem1189141 _27798)). Qed.
Lemma lem1189145 (m : nat) : (term91 m) = False.
Proof. exact (EQ_MP (@lem1189110 m) (@lem1189109 m)). Qed.
Lemma lem1189146 (k : nat) : (term91 k) = False.
Proof. exact (@lem1189145 k). Qed.
Lemma lem1189147 {_27798 : Type'} (k : nat) : (term103 _27798 k) = False.
Proof. exact (TRANS (@lem1189143 _27798 k) (@lem1189146 k)). Qed.
Lemma lem1189148 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1189149 {_27798 : Type'} (k : nat) : (term104 _27798 k) = (and False).
Proof. exact (MK_COMB (@lem1189148) (@lem1189147 _27798 k)). Qed.
Lemma lem1189151 {A : Type'} : (@List.length A (@nil A)) = (NUMERAL 0).
Proof. exact (proj1 (@lem1097080 A)). Qed.
Lemma lem1189152 {_27797 : Type'} : (@List.length _27797 (@nil _27797)) = (NUMERAL 0).
Proof. exact (@lem1189151 _27797). Qed.
Lemma lem1189153 (k : nat) : (Peano.lt k) = (Peano.lt k).
Proof. exact (eq_refl (Peano.lt k)). Qed.
Lemma lem1189154 {_27797 : Type'} (k : nat) : (term103 _27797 k) = (term91 k).
Proof. exact (MK_COMB (@lem1189153 k) (@lem1189152 _27797)). Qed.
Lemma lem1189156 (m : nat) : (term91 m) = False.
Proof. exact (EQ_MP (@lem1189110 m) (@lem1189109 m)). Qed.
Lemma lem1189157 (k : nat) : (term91 k) = False.
Proof. exact (@lem1189156 k). Qed.
Lemma lem1189158 {_27797 : Type'} (k : nat) : (term103 _27797 k) = False.
Proof. exact (TRANS (@lem1189154 _27797 k) (@lem1189157 k)). Qed.
Lemma lem1189159 {_27797 _27798 : Type'} (k : nat) : (term96 _27797 _27798 k) = (False /\ False).
Proof. exact (MK_COMB (@lem1189149 _27798 k) (@lem1189158 _27797 k)). Qed.
Lemma lem1189161 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem1189162 : (False /\ False) = False.
Proof. exact (@lem1189161 False). Qed.
Lemma lem1189163 {_27797 _27798 : Type'} (k : nat) : (term96 _27797 _27798 k) = False.
Proof. exact (TRANS (@lem1189159 _27797 _27798 k) (@lem1189162)). Qed.
Lemma lem1189164 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (k : nat) (q' : Prop) : term105 _27796 _27797 _27798 f k q'.
Proof. exact (@lem1189136 _27796 _27797 _27798 f k False q'). Qed.
Lemma lem1189165 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (k : nat) (q' : Prop) : term106 _27796 _27797 _27798 f k q'.
Proof. exact (@lem1189164 _27796 _27797 _27798 f k q' (@lem1189163 _27797 _27798 k)). Qed.
Lemma lem1189171 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (k : nat) : ((term97 _27796 _27797 _27798 k f) = (term98 _27796 _27797 _27798 f k)) = ((term97 _27796 _27797 _27798 k f) = (term98 _27796 _27797 _27798 f k)).
Proof. exact (eq_refl ((term97 _27796 _27797 _27798 k f) = (term98 _27796 _27797 _27798 f k))). Qed.
Lemma lem1189172 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (k : nat) : term107 _27796 _27797 _27798 f k.
Proof. exact (fun h0 : False => @lem1189171 _27796 _27797 _27798 f k). Qed.
Lemma lem1189173 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (k : nat) : term108 _27796 _27797 _27798 f k.
Proof. exact (@lem1189165 _27796 _27797 _27798 f k ((term97 _27796 _27797 _27798 k f) = (term98 _27796 _27797 _27798 f k))). Qed.
Lemma lem1189174 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (k : nat) : (term109 _27796 _27797 _27798 f k) = (term110 _27796 _27797 _27798 f k).
Proof. exact (@lem1189173 _27796 _27797 _27798 f k (@lem1189172 _27796 _27797 _27798 f k)). Qed.
Lemma lem1189176 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem1189177 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (k : nat) : (term110 _27796 _27797 _27798 f k) = True.
Proof. exact (@lem1189176 ((term97 _27796 _27797 _27798 k f) = (term98 _27796 _27797 _27798 f k))). Qed.
Lemma lem1189178 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (k : nat) : (term109 _27796 _27797 _27798 f k) = True.
Proof. exact (TRANS (@lem1189174 _27796 _27797 _27798 f k) (@lem1189177 _27796 _27797 _27798 f k)). Qed.
Lemma lem1189179 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) : (term111 _27796 _27797 _27798 f) = term112.
Proof. exact (fun_ext (fun k : nat => @lem1189178 _27796 _27797 _27798 f k)). Qed.
Lemma lem1189180 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1189181 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) : (term35 _27796 _27797 _27798 f) = term113.
Proof. exact (MK_COMB (@lem1189180) (@lem1189179 _27796 _27797 _27798 f)). Qed.
Lemma lem1189183 {A : Type'} (t : Prop) : (term114 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1189184 (t : Prop) : (term115 t) = t.
Proof. exact (@lem1189183 nat t). Qed.
Lemma lem1189185 : term113 = True.
Proof. exact (@lem1189184 True). Qed.
Lemma lem1189186 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) : (term35 _27796 _27797 _27798 f) = True.
Proof. exact (TRANS (@lem1189181 _27796 _27797 _27798 f) (@lem1189185)). Qed.
Lemma lem1189187 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) : True = (term35 _27796 _27797 _27798 f).
Proof. exact (SYM (@lem1189186 _27796 _27797 _27798 f)). Qed.
Lemma lem1189188 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) : term35 _27796 _27797 _27798 f.
Proof. exact (EQ_MP (@lem1189187 _27796 _27797 _27798 f) (@lem0)). Qed.
Lemma lem1189189 (m : nat) : term90 m.
Proof. exact (@lem1189024 m). Qed.
Lemma lem1189190 (m : nat) : (term90 m) = ((term91 m) = False).
Proof. exact (eq_refl (term90 m)). Qed.
Lemma lem1189192 {A : Type'} : term116 A.
Proof. exact (proj2 (@lem1097080 A)). Qed.
Lemma lem1189193 {A : Type'} (h : A) : term117 A h.
Proof. exact (@lem1189192 A h). Qed.
Lemma lem1189194 {A : Type'} (h : A) : (term117 A h) = (term118 A h).
Proof. exact (eq_refl (term117 A h)). Qed.
Lemma lem1189195 {A : Type'} (h : A) : term118 A h.
Proof. exact (EQ_MP (@lem1189194 A h) (@lem1189193 A h)). Qed.
Lemma lem1189196 {A : Type'} (h : A) (t : list A) : term119 A h t.
Proof. exact (@lem1189195 A h t). Qed.
Lemma lem1189197 {A : Type'} (h : A) (t : list A) : (term119 A h t) = ((term120 A h t) = (term121 A t)).
Proof. exact (eq_refl (term119 A h t)). Qed.
Lemma lem1189217 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term92 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem1189218 (p : Prop) (q : Prop) (p' : Prop) : term93 p q p'.
Proof. exact (fun q' : Prop => @lem1189217 p q p' q'). Qed.
Lemma lem1189219 (p : Prop) (q : Prop) : term94 p q.
Proof. exact (fun p' : Prop => @lem1189218 p q p'). Qed.
Lemma lem1189220 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (k : nat) (h : _27797) (t : list _27797) : term122 _27796 _27797 _27798 f k h t.
Proof. exact (@lem1189219 (term123 _27797 _27798 k h t) ((term124 _27796 _27797 _27798 k f h t) = (term125 _27796 _27797 _27798 f k h t))). Qed.
Lemma lem1189221 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (k : nat) (h : _27797) (t : list _27797) (p' : Prop) : term126 _27796 _27797 _27798 f k h t p'.
Proof. exact (@lem1189220 _27796 _27797 _27798 f k h t p'). Qed.
Lemma lem1189222 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (k : nat) (h : _27797) (t : list _27797) (p' : Prop) : (term126 _27796 _27797 _27798 f k h t p') = (term127 _27796 _27797 _27798 f k h t p').
Proof. exact (eq_refl (term126 _27796 _27797 _27798 f k h t p')). Qed.
Lemma lem1189223 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (k : nat) (h : _27797) (t : list _27797) (p' : Prop) : term127 _27796 _27797 _27798 f k h t p'.
Proof. exact (EQ_MP (@lem1189222 _27796 _27797 _27798 f k h t p') (@lem1189221 _27796 _27797 _27798 f k h t p')). Qed.
Lemma lem1189224 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (k : nat) (h : _27797) (t : list _27797) (p' : Prop) (q' : Prop) : term128 _27796 _27797 _27798 f k h t p' q'.
Proof. exact (@lem1189223 _27796 _27797 _27798 f k h t p' q'). Qed.
Lemma lem1189225 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (k : nat) (h : _27797) (t : list _27797) (p' : Prop) (q' : Prop) : (term128 _27796 _27797 _27798 f k h t p' q') = (term129 _27796 _27797 _27798 f k h t p' q').
Proof. exact (eq_refl (term128 _27796 _27797 _27798 f k h t p' q')). Qed.
Lemma lem1189226 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (k : nat) (h : _27797) (t : list _27797) (p' : Prop) (q' : Prop) : term129 _27796 _27797 _27798 f k h t p' q'.
Proof. exact (EQ_MP (@lem1189225 _27796 _27797 _27798 f k h t p' q') (@lem1189224 _27796 _27797 _27798 f k h t p' q')). Qed.
Lemma lem1189230 {A : Type'} : (@List.length A (@nil A)) = (NUMERAL 0).
Proof. exact (proj1 (@lem1097080 A)). Qed.
Lemma lem1189231 {_27798 : Type'} : (@List.length _27798 (@nil _27798)) = (NUMERAL 0).
Proof. exact (@lem1189230 _27798). Qed.
Lemma lem1189232 (k : nat) : (Peano.lt k) = (Peano.lt k).
Proof. exact (eq_refl (Peano.lt k)). Qed.
Lemma lem1189233 {_27798 : Type'} (k : nat) : (term103 _27798 k) = (term91 k).
Proof. exact (MK_COMB (@lem1189232 k) (@lem1189231 _27798)). Qed.
Lemma lem1189235 (m : nat) : (term91 m) = False.
Proof. exact (EQ_MP (@lem1189190 m) (@lem1189189 m)). Qed.
Lemma lem1189236 (k : nat) : (term91 k) = False.
Proof. exact (@lem1189235 k). Qed.
Lemma lem1189237 {_27798 : Type'} (k : nat) : (term103 _27798 k) = False.
Proof. exact (TRANS (@lem1189233 _27798 k) (@lem1189236 k)). Qed.
Lemma lem1189238 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1189239 {_27798 : Type'} (k : nat) : (term104 _27798 k) = (and False).
Proof. exact (MK_COMB (@lem1189238) (@lem1189237 _27798 k)). Qed.
Lemma lem1189241 {A : Type'} (h : A) (t : list A) : (term120 A h t) = (term121 A t).
Proof. exact (EQ_MP (@lem1189197 A h t) (@lem1189196 A h t)). Qed.
Lemma lem1189242 {_27797 : Type'} (h : _27797) (t : list _27797) : (term120 _27797 h t) = (term121 _27797 t).
Proof. exact (@lem1189241 _27797 h t). Qed.
Lemma lem1189243 (k : nat) : (Peano.lt k) = (Peano.lt k).
Proof. exact (eq_refl (Peano.lt k)). Qed.
Lemma lem1189244 {_27797 : Type'} (h : _27797) (k : nat) (t : list _27797) : (term130 _27797 k h t) = (term131 _27797 k t).
Proof. exact (MK_COMB (@lem1189243 k) (@lem1189242 _27797 h t)). Qed.
Lemma lem1189245 {_27797 _27798 : Type'} (h : _27797) (k : nat) (t : list _27797) : (term123 _27797 _27798 k h t) = (term132 _27797 k t).
Proof. exact (MK_COMB (@lem1189239 _27798 k) (@lem1189244 _27797 h k t)). Qed.
Lemma lem1189247 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem1189248 {_27797 : Type'} (k : nat) (t : list _27797) : (term132 _27797 k t) = False.
Proof. exact (@lem1189247 (term131 _27797 k t)). Qed.
Lemma lem1189249 {_27797 _27798 : Type'} (k : nat) (h : _27797) (t : list _27797) : (term123 _27797 _27798 k h t) = False.
Proof. exact (TRANS (@lem1189245 _27797 _27798 h k t) (@lem1189248 _27797 k t)). Qed.
Lemma lem1189250 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (k : nat) (h : _27797) (t : list _27797) (q' : Prop) : term133 _27796 _27797 _27798 f k h t q'.
Proof. exact (@lem1189226 _27796 _27797 _27798 f k h t False q'). Qed.
Lemma lem1189251 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (k : nat) (h : _27797) (t : list _27797) (q' : Prop) : term134 _27796 _27797 _27798 f k h t q'.
Proof. exact (@lem1189250 _27796 _27797 _27798 f k h t q' (@lem1189249 _27797 _27798 k h t)). Qed.
Lemma lem1189257 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (k : nat) (h : _27797) (t : list _27797) : ((term124 _27796 _27797 _27798 k f h t) = (term125 _27796 _27797 _27798 f k h t)) = ((term124 _27796 _27797 _27798 k f h t) = (term125 _27796 _27797 _27798 f k h t)).
Proof. exact (eq_refl ((term124 _27796 _27797 _27798 k f h t) = (term125 _27796 _27797 _27798 f k h t))). Qed.
Lemma lem1189258 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (k : nat) (h : _27797) (t : list _27797) : term135 _27796 _27797 _27798 f k h t.
Proof. exact (fun h0 : False => @lem1189257 _27796 _27797 _27798 f k h t). Qed.
Lemma lem1189259 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (k : nat) (h : _27797) (t : list _27797) : term136 _27796 _27797 _27798 f k h t.
Proof. exact (@lem1189251 _27796 _27797 _27798 f k h t ((term124 _27796 _27797 _27798 k f h t) = (term125 _27796 _27797 _27798 f k h t))). Qed.
Lemma lem1189260 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (k : nat) (h : _27797) (t : list _27797) : (term137 _27796 _27797 _27798 f k h t) = (term138 _27796 _27797 _27798 f k h t).
Proof. exact (@lem1189259 _27796 _27797 _27798 f k h t (@lem1189258 _27796 _27797 _27798 f k h t)). Qed.
Lemma lem1189262 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem1189263 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (k : nat) (h : _27797) (t : list _27797) : (term138 _27796 _27797 _27798 f k h t) = True.
Proof. exact (@lem1189262 ((term124 _27796 _27797 _27798 k f h t) = (term125 _27796 _27797 _27798 f k h t))). Qed.
Lemma lem1189264 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (k : nat) (h : _27797) (t : list _27797) : (term137 _27796 _27797 _27798 f k h t) = True.
Proof. exact (TRANS (@lem1189260 _27796 _27797 _27798 f k h t) (@lem1189263 _27796 _27797 _27798 f k h t)). Qed.
Lemma lem1189265 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (h : _27797) (t : list _27797) : (term139 _27796 _27797 _27798 f h t) = term112.
Proof. exact (fun_ext (fun k : nat => @lem1189264 _27796 _27797 _27798 f k h t)). Qed.
Lemma lem1189266 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1189267 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (h : _27797) (t : list _27797) : (term43 _27796 _27797 _27798 f h t) = term113.
Proof. exact (MK_COMB (@lem1189266) (@lem1189265 _27796 _27797 _27798 f h t)). Qed.
Lemma lem1189269 {A : Type'} (t : Prop) : (term114 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1189270 (t : Prop) : (term115 t) = t.
Proof. exact (@lem1189269 nat t). Qed.
Lemma lem1189271 : term113 = True.
Proof. exact (@lem1189270 True). Qed.
Lemma lem1189272 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (h : _27797) (t : list _27797) : (term43 _27796 _27797 _27798 f h t) = True.
Proof. exact (TRANS (@lem1189267 _27796 _27797 _27798 f h t) (@lem1189271)). Qed.
Lemma lem1189273 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (h : _27797) (t : list _27797) : True = (term43 _27796 _27797 _27798 f h t).
Proof. exact (SYM (@lem1189272 _27796 _27797 _27798 f h t)). Qed.
Lemma lem1189274 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (h : _27797) (t : list _27797) : term43 _27796 _27797 _27798 f h t.
Proof. exact (EQ_MP (@lem1189273 _27796 _27797 _27798 f h t) (@lem0)). Qed.
Lemma lem1189275 (m : nat) : term90 m.
Proof. exact (@lem1189024 m). Qed.
Lemma lem1189276 (m : nat) : (term90 m) = ((term91 m) = False).
Proof. exact (eq_refl (term90 m)). Qed.
Lemma lem1189278 {A : Type'} : term116 A.
Proof. exact (proj2 (@lem1097080 A)). Qed.
Lemma lem1189279 {A : Type'} (h : A) : term117 A h.
Proof. exact (@lem1189278 A h). Qed.
Lemma lem1189280 {A : Type'} (h : A) : (term117 A h) = (term118 A h).
Proof. exact (eq_refl (term117 A h)). Qed.
Lemma lem1189281 {A : Type'} (h : A) : term118 A h.
Proof. exact (EQ_MP (@lem1189280 A h) (@lem1189279 A h)). Qed.
Lemma lem1189282 {A : Type'} (h : A) (t : list A) : term119 A h t.
Proof. exact (@lem1189281 A h t). Qed.
Lemma lem1189283 {A : Type'} (h : A) (t : list A) : (term119 A h t) = ((term120 A h t) = (term121 A t)).
Proof. exact (eq_refl (term119 A h t)). Qed.
Lemma lem1189306 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term92 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem1189307 (p : Prop) (q : Prop) (p' : Prop) : term93 p q p'.
Proof. exact (fun q' : Prop => @lem1189306 p q p' q'). Qed.
Lemma lem1189308 (p : Prop) (q : Prop) : term94 p q.
Proof. exact (fun p' : Prop => @lem1189307 p q p'). Qed.
Lemma lem1189309 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (h : _27798) (t : list _27798) (k : nat) : term140 _27796 _27797 _27798 f h t k.
Proof. exact (@lem1189308 (term141 _27797 _27798 h t k) ((term142 _27796 _27797 _27798 k f h t) = (term143 _27796 _27797 _27798 f h t k))). Qed.
Lemma lem1189310 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (h : _27798) (t : list _27798) (k : nat) (p' : Prop) : term144 _27796 _27797 _27798 f h t k p'.
Proof. exact (@lem1189309 _27796 _27797 _27798 f h t k p'). Qed.
Lemma lem1189311 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (h : _27798) (t : list _27798) (k : nat) (p' : Prop) : (term144 _27796 _27797 _27798 f h t k p') = (term145 _27796 _27797 _27798 f h t k p').
Proof. exact (eq_refl (term144 _27796 _27797 _27798 f h t k p')). Qed.
Lemma lem1189312 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (h : _27798) (t : list _27798) (k : nat) (p' : Prop) : term145 _27796 _27797 _27798 f h t k p'.
Proof. exact (EQ_MP (@lem1189311 _27796 _27797 _27798 f h t k p') (@lem1189310 _27796 _27797 _27798 f h t k p')). Qed.
Lemma lem1189313 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (h : _27798) (t : list _27798) (k : nat) (p' : Prop) (q' : Prop) : term146 _27796 _27797 _27798 f h t k p' q'.
Proof. exact (@lem1189312 _27796 _27797 _27798 f h t k p' q'). Qed.
Lemma lem1189314 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (h : _27798) (t : list _27798) (k : nat) (p' : Prop) (q' : Prop) : (term146 _27796 _27797 _27798 f h t k p' q') = (term147 _27796 _27797 _27798 f h t k p' q').
Proof. exact (eq_refl (term146 _27796 _27797 _27798 f h t k p' q')). Qed.
Lemma lem1189315 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (h : _27798) (t : list _27798) (k : nat) (p' : Prop) (q' : Prop) : term147 _27796 _27797 _27798 f h t k p' q'.
Proof. exact (EQ_MP (@lem1189314 _27796 _27797 _27798 f h t k p' q') (@lem1189313 _27796 _27797 _27798 f h t k p' q')). Qed.
Lemma lem1189319 {A : Type'} (h : A) (t : list A) : (term120 A h t) = (term121 A t).
Proof. exact (EQ_MP (@lem1189283 A h t) (@lem1189282 A h t)). Qed.
Lemma lem1189320 {_27798 : Type'} (h : _27798) (t : list _27798) : (term120 _27798 h t) = (term121 _27798 t).
Proof. exact (@lem1189319 _27798 h t). Qed.
Lemma lem1189321 (k : nat) : (Peano.lt k) = (Peano.lt k).
Proof. exact (eq_refl (Peano.lt k)). Qed.
Lemma lem1189322 {_27798 : Type'} (h : _27798) (k : nat) (t : list _27798) : (term130 _27798 k h t) = (term131 _27798 k t).
Proof. exact (MK_COMB (@lem1189321 k) (@lem1189320 _27798 h t)). Qed.
Lemma lem1189323 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1189324 {_27798 : Type'} (h : _27798) (k : nat) (t : list _27798) : (term148 _27798 k h t) = (term149 _27798 k t).
Proof. exact (MK_COMB (@lem1189323) (@lem1189322 _27798 h k t)). Qed.
Lemma lem1189326 {A : Type'} : (@List.length A (@nil A)) = (NUMERAL 0).
Proof. exact (proj1 (@lem1097080 A)). Qed.
Lemma lem1189327 {_27797 : Type'} : (@List.length _27797 (@nil _27797)) = (NUMERAL 0).
Proof. exact (@lem1189326 _27797). Qed.
Lemma lem1189328 (k : nat) : (Peano.lt k) = (Peano.lt k).
Proof. exact (eq_refl (Peano.lt k)). Qed.
Lemma lem1189329 {_27797 : Type'} (k : nat) : (term103 _27797 k) = (term91 k).
Proof. exact (MK_COMB (@lem1189328 k) (@lem1189327 _27797)). Qed.
Lemma lem1189331 (m : nat) : (term91 m) = False.
Proof. exact (EQ_MP (@lem1189276 m) (@lem1189275 m)). Qed.
Lemma lem1189332 (k : nat) : (term91 k) = False.
Proof. exact (@lem1189331 k). Qed.
Lemma lem1189333 {_27797 : Type'} (k : nat) : (term103 _27797 k) = False.
Proof. exact (TRANS (@lem1189329 _27797 k) (@lem1189332 k)). Qed.
Lemma lem1189334 {_27797 _27798 : Type'} (h : _27798) (k : nat) (t : list _27798) : (term141 _27797 _27798 h t k) = (term150 _27798 k t).
Proof. exact (MK_COMB (@lem1189324 _27798 h k t) (@lem1189333 _27797 k)). Qed.
Lemma lem1189336 (t : Prop) : (t /\ False) = False.
Proof. exact (proj1 (@lem1845 t)). Qed.
Lemma lem1189337 {_27798 : Type'} (k : nat) (t : list _27798) : (term150 _27798 k t) = False.
Proof. exact (@lem1189336 (term131 _27798 k t)). Qed.
Lemma lem1189338 {_27797 _27798 : Type'} (h : _27798) (t : list _27798) (k : nat) : (term141 _27797 _27798 h t k) = False.
Proof. exact (TRANS (@lem1189334 _27797 _27798 h k t) (@lem1189337 _27798 k t)). Qed.
Lemma lem1189339 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (h : _27798) (t : list _27798) (k : nat) (q' : Prop) : term151 _27796 _27797 _27798 f h t k q'.
Proof. exact (@lem1189315 _27796 _27797 _27798 f h t k False q'). Qed.
Lemma lem1189340 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (h : _27798) (t : list _27798) (k : nat) (q' : Prop) : term152 _27796 _27797 _27798 f h t k q'.
Proof. exact (@lem1189339 _27796 _27797 _27798 f h t k q' (@lem1189338 _27797 _27798 h t k)). Qed.
Lemma lem1189346 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (h : _27798) (t : list _27798) (k : nat) : ((term142 _27796 _27797 _27798 k f h t) = (term143 _27796 _27797 _27798 f h t k)) = ((term142 _27796 _27797 _27798 k f h t) = (term143 _27796 _27797 _27798 f h t k)).
Proof. exact (eq_refl ((term142 _27796 _27797 _27798 k f h t) = (term143 _27796 _27797 _27798 f h t k))). Qed.
Lemma lem1189347 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (h : _27798) (t : list _27798) (k : nat) : term153 _27796 _27797 _27798 f h t k.
Proof. exact (fun h0 : False => @lem1189346 _27796 _27797 _27798 f h t k). Qed.
Lemma lem1189348 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (h : _27798) (t : list _27798) (k : nat) : term154 _27796 _27797 _27798 f h t k.
Proof. exact (@lem1189340 _27796 _27797 _27798 f h t k ((term142 _27796 _27797 _27798 k f h t) = (term143 _27796 _27797 _27798 f h t k))). Qed.
Lemma lem1189349 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (h : _27798) (t : list _27798) (k : nat) : (term155 _27796 _27797 _27798 f h t k) = (term156 _27796 _27797 _27798 f h t k).
Proof. exact (@lem1189348 _27796 _27797 _27798 f h t k (@lem1189347 _27796 _27797 _27798 f h t k)). Qed.
Lemma lem1189351 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem1189352 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (h : _27798) (t : list _27798) (k : nat) : (term156 _27796 _27797 _27798 f h t k) = True.
Proof. exact (@lem1189351 ((term142 _27796 _27797 _27798 k f h t) = (term143 _27796 _27797 _27798 f h t k))). Qed.
Lemma lem1189353 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (h : _27798) (t : list _27798) (k : nat) : (term155 _27796 _27797 _27798 f h t k) = True.
Proof. exact (TRANS (@lem1189349 _27796 _27797 _27798 f h t k) (@lem1189352 _27796 _27797 _27798 f h t k)). Qed.
Lemma lem1189354 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (h : _27798) (t : list _27798) : (term157 _27796 _27797 _27798 f h t) = term112.
Proof. exact (fun_ext (fun k : nat => @lem1189353 _27796 _27797 _27798 f h t k)). Qed.
Lemma lem1189355 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1189356 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (h : _27798) (t : list _27798) : (term64 _27796 _27797 _27798 f h t) = term113.
Proof. exact (MK_COMB (@lem1189355) (@lem1189354 _27796 _27797 _27798 f h t)). Qed.
Lemma lem1189358 {A : Type'} (t : Prop) : (term114 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1189359 (t : Prop) : (term115 t) = t.
Proof. exact (@lem1189358 nat t). Qed.
Lemma lem1189360 : term113 = True.
Proof. exact (@lem1189359 True). Qed.
Lemma lem1189361 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (h : _27798) (t : list _27798) : (term64 _27796 _27797 _27798 f h t) = True.
Proof. exact (TRANS (@lem1189356 _27796 _27797 _27798 f h t) (@lem1189360)). Qed.
Lemma lem1189362 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (h : _27798) (t : list _27798) : True = (term64 _27796 _27797 _27798 f h t).
Proof. exact (SYM (@lem1189361 _27796 _27797 _27798 f h t)). Qed.
Lemma lem1189363 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (h : _27798) (t : list _27798) : term64 _27796 _27797 _27798 f h t.
Proof. exact (EQ_MP (@lem1189362 _27796 _27797 _27798 f h t) (@lem0)). Qed.
Lemma lem1189367 {A : Type'} : term116 A.
Proof. exact (proj2 (@lem1097080 A)). Qed.
Lemma lem1189368 {A : Type'} (h : A) : term117 A h.
Proof. exact (@lem1189367 A h). Qed.
Lemma lem1189369 {A : Type'} (h : A) : (term117 A h) = (term118 A h).
Proof. exact (eq_refl (term117 A h)). Qed.
Lemma lem1189370 {A : Type'} (h : A) : term118 A h.
Proof. exact (EQ_MP (@lem1189369 A h) (@lem1189368 A h)). Qed.
Lemma lem1189371 {A : Type'} (h : A) (t : list A) : term119 A h t.
Proof. exact (@lem1189370 A h t). Qed.
Lemma lem1189372 {A : Type'} (h : A) (t : list A) : (term119 A h t) = ((term120 A h t) = (term121 A t)).
Proof. exact (eq_refl (term119 A h t)). Qed.
Lemma lem1189405 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term92 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem1189406 (p : Prop) (q : Prop) (p' : Prop) : term93 p q p'.
Proof. exact (fun q' : Prop => @lem1189405 p q p' q'). Qed.
Lemma lem1189407 (p : Prop) (q : Prop) : term94 p q.
Proof. exact (fun p' : Prop => @lem1189406 p q p'). Qed.
Lemma lem1189408 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (h : _27798) (t : list _27798) (k : nat) (h' : _27797) (t' : list _27797) : term158 _27796 _27797 _27798 f h t k h' t'.
Proof. exact (@lem1189407 (term159 _27797 _27798 h t k h' t') ((term160 _27796 _27797 _27798 k f h t h' t') = (term161 _27796 _27797 _27798 f h t k h' t'))). Qed.
Lemma lem1189409 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (h : _27798) (t : list _27798) (k : nat) (h' : _27797) (t' : list _27797) (p' : Prop) : term162 _27796 _27797 _27798 f h t k h' t' p'.
Proof. exact (@lem1189408 _27796 _27797 _27798 f h t k h' t' p'). Qed.
Lemma lem1189410 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (h : _27798) (t : list _27798) (k : nat) (h' : _27797) (t' : list _27797) (p' : Prop) : (term162 _27796 _27797 _27798 f h t k h' t' p') = (term163 _27796 _27797 _27798 f h t k h' t' p').
Proof. exact (eq_refl (term162 _27796 _27797 _27798 f h t k h' t' p')). Qed.
Lemma lem1189411 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (h : _27798) (t : list _27798) (k : nat) (h' : _27797) (t' : list _27797) (p' : Prop) : term163 _27796 _27797 _27798 f h t k h' t' p'.
Proof. exact (EQ_MP (@lem1189410 _27796 _27797 _27798 f h t k h' t' p') (@lem1189409 _27796 _27797 _27798 f h t k h' t' p')). Qed.
Lemma lem1189412 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (h : _27798) (t : list _27798) (k : nat) (h' : _27797) (t' : list _27797) (p' : Prop) (q' : Prop) : term164 _27796 _27797 _27798 f h t k h' t' p' q'.
Proof. exact (@lem1189411 _27796 _27797 _27798 f h t k h' t' p' q'). Qed.
Lemma lem1189413 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (h : _27798) (t : list _27798) (k : nat) (h' : _27797) (t' : list _27797) (p' : Prop) (q' : Prop) : (term164 _27796 _27797 _27798 f h t k h' t' p' q') = (term165 _27796 _27797 _27798 f h t k h' t' p' q').
Proof. exact (eq_refl (term164 _27796 _27797 _27798 f h t k h' t' p' q')). Qed.
Lemma lem1189414 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (h : _27798) (t : list _27798) (k : nat) (h' : _27797) (t' : list _27797) (p' : Prop) (q' : Prop) : term165 _27796 _27797 _27798 f h t k h' t' p' q'.
Proof. exact (EQ_MP (@lem1189413 _27796 _27797 _27798 f h t k h' t' p' q') (@lem1189412 _27796 _27797 _27798 f h t k h' t' p' q')). Qed.
Lemma lem1189418 {A : Type'} (h : A) (t : list A) : (term120 A h t) = (term121 A t).
Proof. exact (EQ_MP (@lem1189372 A h t) (@lem1189371 A h t)). Qed.
Lemma lem1189419 {_27798 : Type'} (h : _27798) (t : list _27798) : (term120 _27798 h t) = (term121 _27798 t).
Proof. exact (@lem1189418 _27798 h t). Qed.
Lemma lem1189420 (k : nat) : (Peano.lt k) = (Peano.lt k).
Proof. exact (eq_refl (Peano.lt k)). Qed.
Lemma lem1189421 {_27798 : Type'} (h : _27798) (k : nat) (t : list _27798) : (term130 _27798 k h t) = (term131 _27798 k t).
Proof. exact (MK_COMB (@lem1189420 k) (@lem1189419 _27798 h t)). Qed.
Lemma lem1189422 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1189423 {_27798 : Type'} (h : _27798) (k : nat) (t : list _27798) : (term148 _27798 k h t) = (term149 _27798 k t).
Proof. exact (MK_COMB (@lem1189422) (@lem1189421 _27798 h k t)). Qed.
Lemma lem1189425 {A : Type'} (h : A) (t : list A) : (term120 A h t) = (term121 A t).
Proof. exact (EQ_MP (@lem1189372 A h t) (@lem1189371 A h t)). Qed.
Lemma lem1189426 {_27797 : Type'} (h : _27797) (t : list _27797) : (term120 _27797 h t) = (term121 _27797 t).
Proof. exact (@lem1189425 _27797 h t). Qed.
Lemma lem1189427 {_27797 : Type'} (h' : _27797) (t' : list _27797) : (term120 _27797 h' t') = (term121 _27797 t').
Proof. exact (@lem1189426 _27797 h' t'). Qed.
Lemma lem1189428 (k : nat) : (Peano.lt k) = (Peano.lt k).
Proof. exact (eq_refl (Peano.lt k)). Qed.
Lemma lem1189429 {_27797 : Type'} (h' : _27797) (k : nat) (t' : list _27797) : (term130 _27797 k h' t') = (term131 _27797 k t').
Proof. exact (MK_COMB (@lem1189428 k) (@lem1189427 _27797 h' t')). Qed.
Lemma lem1189430 {_27797 _27798 : Type'} (h : _27798) (h' : _27797) (t : list _27798) (k : nat) (t' : list _27797) : (term159 _27797 _27798 h t k h' t') = (term166 _27797 _27798 t k t').
Proof. exact (MK_COMB (@lem1189423 _27798 h k t) (@lem1189429 _27797 h' k t')). Qed.
Lemma lem1189433 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (h : _27798) (h' : _27797) (t : list _27798) (k : nat) (t' : list _27797) (q' : Prop) : term167 _27796 _27797 _27798 f h h' t k t' q'.
Proof. exact (@lem1189414 _27796 _27797 _27798 f h t k h' t' (term166 _27797 _27798 t k t') q'). Qed.
Lemma lem1189434 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (h : _27798) (h' : _27797) (t : list _27798) (k : nat) (t' : list _27797) (q' : Prop) : term168 _27796 _27797 _27798 f h h' t k t' q'.
Proof. exact (@lem1189433 _27796 _27797 _27798 f h h' t k t' q' (@lem1189430 _27797 _27798 h h' t k t')). Qed.
Lemma lem1189444 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (h : _27798) (t : list _27798) (k : nat) (h' : _27797) (t' : list _27797) : ((term160 _27796 _27797 _27798 k f h t h' t') = (term161 _27796 _27797 _27798 f h t k h' t')) = ((term160 _27796 _27797 _27798 k f h t h' t') = (term161 _27796 _27797 _27798 f h t k h' t')).
Proof. exact (eq_refl ((term160 _27796 _27797 _27798 k f h t h' t') = (term161 _27796 _27797 _27798 f h t k h' t'))). Qed.
Lemma lem1189445 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (h : _27798) (t : list _27798) (k : nat) (h' : _27797) (t' : list _27797) : term169 _27796 _27797 _27798 f h t k h' t'.
Proof. exact (fun h0 : term166 _27797 _27798 t k t' => @lem1189444 _27796 _27797 _27798 f h t k h' t'). Qed.
Lemma lem1189446 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (h : _27798) (t : list _27798) (k : nat) (h' : _27797) (t' : list _27797) : term170 _27796 _27797 _27798 f h t k h' t'.
Proof. exact (@lem1189434 _27796 _27797 _27798 f h h' t k t' ((term160 _27796 _27797 _27798 k f h t h' t') = (term161 _27796 _27797 _27798 f h t k h' t'))). Qed.
Lemma lem1189447 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (h : _27798) (t : list _27798) (k : nat) (h' : _27797) (t' : list _27797) : (term171 _27796 _27797 _27798 f h t k h' t') = (term172 _27796 _27797 _27798 f h t k h' t').
Proof. exact (@lem1189446 _27796 _27797 _27798 f h t k h' t' (@lem1189445 _27796 _27797 _27798 f h t k h' t')). Qed.
Lemma lem1189483 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (h : _27798) (t : list _27798) (h' : _27797) (t' : list _27797) : (term173 _27796 _27797 _27798 f h t h' t') = (term174 _27796 _27797 _27798 f h t h' t').
Proof. exact (fun_ext (fun k : nat => @lem1189447 _27796 _27797 _27798 f h t k h' t')). Qed.
Lemma lem1189519 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1189520 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (h : _27798) (t : list _27798) (h' : _27797) (t' : list _27797) : (term72 _27796 _27797 _27798 f h t h' t') = (term175 _27796 _27797 _27798 f h t h' t').
Proof. exact (MK_COMB (@lem1189519) (@lem1189483 _27796 _27797 _27798 f h t h' t')). Qed.
Lemma lem1189560 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (h : _27798) (t : list _27798) (h' : _27797) (t' : list _27797) : (term175 _27796 _27797 _27798 f h t h' t') = (term72 _27796 _27797 _27798 f h t h' t').
Proof. exact (SYM (@lem1189520 _27796 _27797 _27798 f h t h' t')). Qed.
Lemma lem1189562 (P : nat -> Prop) : term176 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem1189563 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (h : _27798) (t : list _27798) (h' : _27797) (t' : list _27797) : term177 _27796 _27797 _27798 f h t h' t'.
Proof. exact (@lem1189562 (term174 _27796 _27797 _27798 f h t h' t')). Qed.
Lemma lem1189564 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (h : _27798) (t : list _27798) (h' : _27797) (t' : list _27797) : (term178 _27796 _27797 _27798 f h t h' t') = (term179 _27796 _27797 _27798 f h t h' t').
Proof. exact (eq_refl (term178 _27796 _27797 _27798 f h t h' t')). Qed.
Lemma lem1189565 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1189566 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (h : _27798) (t : list _27798) (h' : _27797) (t' : list _27797) : (term180 _27796 _27797 _27798 f h t h' t') = (term181 _27796 _27797 _27798 f h t h' t').
Proof. exact (MK_COMB (@lem1189565) (@lem1189564 _27796 _27797 _27798 f h t h' t')). Qed.
Lemma lem1189567 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (h : _27798) (t : list _27798) (k : nat) (h' : _27797) (t' : list _27797) : (term182 _27796 _27797 _27798 f h t h' t' k) = (term172 _27796 _27797 _27798 f h t k h' t').
Proof. exact (eq_refl (term182 _27796 _27797 _27798 f h t h' t' k)). Qed.
Lemma lem1189568 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1189569 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (h : _27798) (t : list _27798) (k : nat) (h' : _27797) (t' : list _27797) : (term183 _27796 _27797 _27798 f h t h' t' k) = (term184 _27796 _27797 _27798 f h t k h' t').
Proof. exact (MK_COMB (@lem1189568) (@lem1189567 _27796 _27797 _27798 f h t k h' t')). Qed.
Lemma lem1189570 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (h : _27798) (t : list _27798) (k : nat) (h' : _27797) (t' : list _27797) : (term185 _27796 _27797 _27798 f h t h' t' k) = (term186 _27796 _27797 _27798 f h t k h' t').
Proof. exact (eq_refl (term185 _27796 _27797 _27798 f h t h' t' k)). Qed.
Lemma lem1189571 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (h : _27798) (t : list _27798) (k : nat) (h' : _27797) (t' : list _27797) : (term187 _27796 _27797 _27798 f h t h' t' k) = (term188 _27796 _27797 _27798 f h t k h' t').
Proof. exact (MK_COMB (@lem1189569 _27796 _27797 _27798 f h t k h' t') (@lem1189570 _27796 _27797 _27798 f h t k h' t')). Qed.
Lemma lem1189572 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (h : _27798) (t : list _27798) (h' : _27797) (t' : list _27797) : (term189 _27796 _27797 _27798 f h t h' t') = (term190 _27796 _27797 _27798 f h t h' t').
Proof. exact (fun_ext (fun k : nat => @lem1189571 _27796 _27797 _27798 f h t k h' t')). Qed.
Lemma lem1189573 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1189574 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (h : _27798) (t : list _27798) (h' : _27797) (t' : list _27797) : (term191 _27796 _27797 _27798 f h t h' t') = (term192 _27796 _27797 _27798 f h t h' t').
Proof. exact (MK_COMB (@lem1189573) (@lem1189572 _27796 _27797 _27798 f h t h' t')). Qed.
Lemma lem1189575 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (h : _27798) (t : list _27798) (h' : _27797) (t' : list _27797) : (term193 _27796 _27797 _27798 f h t h' t') = (term194 _27796 _27797 _27798 f h t h' t').
Proof. exact (MK_COMB (@lem1189566 _27796 _27797 _27798 f h t h' t') (@lem1189574 _27796 _27797 _27798 f h t h' t')). Qed.
Lemma lem1189576 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1189577 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (h : _27798) (t : list _27798) (h' : _27797) (t' : list _27797) : (term195 _27796 _27797 _27798 f h t h' t') = (term196 _27796 _27797 _27798 f h t h' t').
Proof. exact (MK_COMB (@lem1189576) (@lem1189575 _27796 _27797 _27798 f h t h' t')). Qed.
Lemma lem1189578 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (h : _27798) (t : list _27798) (k : nat) (h' : _27797) (t' : list _27797) : (term182 _27796 _27797 _27798 f h t h' t' k) = (term172 _27796 _27797 _27798 f h t k h' t').
Proof. exact (eq_refl (term182 _27796 _27797 _27798 f h t h' t' k)). Qed.
Lemma lem1189579 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (h : _27798) (t : list _27798) (h' : _27797) (t' : list _27797) : (term197 _27796 _27797 _27798 f h t h' t') = (term174 _27796 _27797 _27798 f h t h' t').
Proof. exact (fun_ext (fun k : nat => @lem1189578 _27796 _27797 _27798 f h t k h' t')). Qed.
Lemma lem1189580 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1189581 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (h : _27798) (t : list _27798) (h' : _27797) (t' : list _27797) : (term198 _27796 _27797 _27798 f h t h' t') = (term175 _27796 _27797 _27798 f h t h' t').
Proof. exact (MK_COMB (@lem1189580) (@lem1189579 _27796 _27797 _27798 f h t h' t')). Qed.
Lemma lem1189582 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (h : _27798) (t : list _27798) (h' : _27797) (t' : list _27797) : (term177 _27796 _27797 _27798 f h t h' t') = (term199 _27796 _27797 _27798 f h t h' t').
Proof. exact (MK_COMB (@lem1189577 _27796 _27797 _27798 f h t h' t') (@lem1189581 _27796 _27797 _27798 f h t h' t')). Qed.
Lemma lem1189583 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (h : _27798) (t : list _27798) (h' : _27797) (t' : list _27797) : term199 _27796 _27797 _27798 f h t h' t'.
Proof. exact (EQ_MP (@lem1189582 _27796 _27797 _27798 f h t h' t') (@lem1189563 _27796 _27797 _27798 f h t h' t')). Qed.
Lemma lem1189629 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term92 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem1189630 (p : Prop) (q : Prop) (p' : Prop) : term93 p q p'.
Proof. exact (fun q' : Prop => @lem1189629 p q p' q'). Qed.
Lemma lem1189631 (p : Prop) (q : Prop) : term94 p q.
Proof. exact (fun p' : Prop => @lem1189630 p q p'). Qed.
Lemma lem1189632 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (h : _27798) (t : list _27798) (h' : _27797) (t' : list _27797) : term200 _27796 _27797 _27798 f h t h' t'.
Proof. exact (@lem1189631 (term201 _27797 _27798 t t') ((term202 _27796 _27797 _27798 f h t h' t') = (term203 _27796 _27797 _27798 f h t h' t'))). Qed.
Lemma lem1189633 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (h : _27798) (t : list _27798) (h' : _27797) (t' : list _27797) (p' : Prop) : term204 _27796 _27797 _27798 f h t h' t' p'.
Proof. exact (@lem1189632 _27796 _27797 _27798 f h t h' t' p'). Qed.
Lemma lem1189634 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (h : _27798) (t : list _27798) (h' : _27797) (t' : list _27797) (p' : Prop) : (term204 _27796 _27797 _27798 f h t h' t' p') = (term205 _27796 _27797 _27798 f h t h' t' p').
Proof. exact (eq_refl (term204 _27796 _27797 _27798 f h t h' t' p')). Qed.
Lemma lem1189635 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (h : _27798) (t : list _27798) (h' : _27797) (t' : list _27797) (p' : Prop) : term205 _27796 _27797 _27798 f h t h' t' p'.
Proof. exact (EQ_MP (@lem1189634 _27796 _27797 _27798 f h t h' t' p') (@lem1189633 _27796 _27797 _27798 f h t h' t' p')). Qed.
Lemma lem1189636 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (h : _27798) (t : list _27798) (h' : _27797) (t' : list _27797) (p' : Prop) (q' : Prop) : term206 _27796 _27797 _27798 f h t h' t' p' q'.
Proof. exact (@lem1189635 _27796 _27797 _27798 f h t h' t' p' q'). Qed.
Lemma lem1189637 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (h : _27798) (t : list _27798) (h' : _27797) (t' : list _27797) (p' : Prop) (q' : Prop) : (term206 _27796 _27797 _27798 f h t h' t' p' q') = (term207 _27796 _27797 _27798 f h t h' t' p' q').
Proof. exact (eq_refl (term206 _27796 _27797 _27798 f h t h' t' p' q')). Qed.
Lemma lem1189638 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (h : _27798) (t : list _27798) (h' : _27797) (t' : list _27797) (p' : Prop) (q' : Prop) : term207 _27796 _27797 _27798 f h t h' t' p' q'.
Proof. exact (EQ_MP (@lem1189637 _27796 _27797 _27798 f h t h' t' p' q') (@lem1189636 _27796 _27797 _27798 f h t h' t' p' q')). Qed.
Lemma lem1189641 {_27797 _27798 : Type'} (t : list _27798) (t' : list _27797) : (term201 _27797 _27798 t t') = (term201 _27797 _27798 t t').
Proof. exact (eq_refl (term201 _27797 _27798 t t')). Qed.
Lemma lem1189642 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (h : _27798) (h' : _27797) (t : list _27798) (t' : list _27797) (q' : Prop) : term208 _27796 _27797 _27798 f h h' t t' q'.
Proof. exact (@lem1189638 _27796 _27797 _27798 f h t h' t' (term201 _27797 _27798 t t') q'). Qed.
Lemma lem1189643 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (h : _27798) (h' : _27797) (t : list _27798) (t' : list _27797) (q' : Prop) : term209 _27796 _27797 _27798 f h h' t t' q'.
Proof. exact (@lem1189642 _27796 _27797 _27798 f h h' t t' q' (@lem1189641 _27797 _27798 t t')). Qed.
Lemma lem1189654 {_25569 : Type'} (l : list _25569) : (term210 _25569 l) = (@hd _25569 l).
Proof. exact (EQ_MP (@lem1105742 _25569 l) (@lem1105741 _25569 l)). Qed.
Lemma lem1189655 {_27796 : Type'} (l : list _27796) : (term210 _27796 l) = (@hd _27796 l).
Proof. exact (@lem1189654 _27796 l). Qed.
Lemma lem1189656 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (h : _27798) (t : list _27798) (h' : _27797) (t' : list _27797) : (term202 _27796 _27797 _27798 f h t h' t') = (term211 _27796 _27797 _27798 f h t h' t').
Proof. exact (@lem1189655 _27796 (term212 _27796 _27797 _27798 f h t h' t')). Qed.
Lemma lem1189658 {_25542 _25543 _25549 : Type'} (h1' : _25543) (h2' : _25542) (f : type1469 _25542 _25543 _25549) (t1 : list _25543) (t2 : list _25542) : (term213 _25542 _25543 _25549 f h1' t1 h2' t2) = (term214 _25542 _25543 _25549 h1' h2' f t1 t2).
Proof. exact (proj2 (@lem1105126 _25542 _25543 _25549 h1' h2' f t1 t2)). Qed.
Lemma lem1189659 {_27796 _27797 _27798 : Type'} (h1' : _27798) (h2' : _27797) (f : type1518 _27796 _27797 _27798) (t1 : list _27798) (t2 : list _27797) : (term212 _27796 _27797 _27798 f h1' t1 h2' t2) = (term215 _27796 _27797 _27798 h1' h2' f t1 t2).
Proof. exact (@lem1189658 _27797 _27798 _27796 h1' h2' f t1 t2). Qed.
Lemma lem1189660 {_27796 _27797 _27798 : Type'} (h : _27798) (h' : _27797) (f : type1518 _27796 _27797 _27798) (t : list _27798) (t' : list _27797) : (term212 _27796 _27797 _27798 f h t h' t') = (term215 _27796 _27797 _27798 h h' f t t').
Proof. exact (@lem1189659 _27796 _27797 _27798 h h' f t t'). Qed.
Lemma lem1189661 {_27796 : Type'} : (@hd _27796) = (@hd _27796).
Proof. exact (eq_refl (@hd _27796)). Qed.
Lemma lem1189662 {_27796 _27797 _27798 : Type'} (h : _27798) (h' : _27797) (f : type1518 _27796 _27797 _27798) (t : list _27798) (t' : list _27797) : (term211 _27796 _27797 _27798 f h t h' t') = (term216 _27796 _27797 _27798 h h' f t t').
Proof. exact (MK_COMB (@lem1189661 _27796) (@lem1189660 _27796 _27797 _27798 h h' f t t')). Qed.
Lemma lem1189664 {A : Type'} (t : list A) (h : A) : (term217 A h t) = h.
Proof. exact (EQ_MP (@lem1094866 A t h) (@lem1094865 A t h)). Qed.
Lemma lem1189665 {_27796 : Type'} (t : list _27796) (h : _27796) : (term217 _27796 h t) = h.
Proof. exact (@lem1189664 _27796 t h). Qed.
Lemma lem1189666 {_27796 _27797 _27798 : Type'} (t : list _27798) (t' : list _27797) (f : type1518 _27796 _27797 _27798) (h : _27798) (h' : _27797) : (term216 _27796 _27797 _27798 h h' f t t') = (f h h').
Proof. exact (@lem1189665 _27796 (@MAP2 _27796 _27798 _27797 f t t') (f h h')). Qed.
Lemma lem1189667 {_27796 _27797 _27798 : Type'} (t : list _27798) (t' : list _27797) (f : type1518 _27796 _27797 _27798) (h : _27798) (h' : _27797) : (term211 _27796 _27797 _27798 f h t h' t') = (f h h').
Proof. exact (TRANS (@lem1189662 _27796 _27797 _27798 h h' f t t') (@lem1189666 _27796 _27797 _27798 t t' f h h')). Qed.
Lemma lem1189668 {_27796 _27797 _27798 : Type'} (t : list _27798) (t' : list _27797) (f : type1518 _27796 _27797 _27798) (h : _27798) (h' : _27797) : (term202 _27796 _27797 _27798 f h t h' t') = (f h h').
Proof. exact (TRANS (@lem1189656 _27796 _27797 _27798 f h t h' t') (@lem1189667 _27796 _27797 _27798 t t' f h h')). Qed.
Lemma lem1189669 {_27796 : Type'} : (@eq _27796) = (@eq _27796).
Proof. exact (eq_refl (@eq _27796)). Qed.
Lemma lem1189670 {_27796 _27797 _27798 : Type'} (t : list _27798) (t' : list _27797) (f : type1518 _27796 _27797 _27798) (h : _27798) (h' : _27797) : (term218 _27796 _27797 _27798 f h t h' t') = (term219 _27796 _27797 _27798 f h h').
Proof. exact (MK_COMB (@lem1189669 _27796) (@lem1189668 _27796 _27797 _27798 t t' f h h')). Qed.
Lemma lem1189672 {_25569 : Type'} (l : list _25569) : (term210 _25569 l) = (@hd _25569 l).
Proof. exact (EQ_MP (@lem1105742 _25569 l) (@lem1105741 _25569 l)). Qed.
Lemma lem1189673 {_27798 : Type'} (l : list _27798) : (term210 _27798 l) = (@hd _27798 l).
Proof. exact (@lem1189672 _27798 l). Qed.
Lemma lem1189674 {_27798 : Type'} (h : _27798) (t : list _27798) : (term220 _27798 h t) = (term217 _27798 h t).
Proof. exact (@lem1189673 _27798 (@cons _27798 h t)). Qed.
Lemma lem1189676 {A : Type'} (t : list A) (h : A) : (term217 A h t) = h.
Proof. exact (EQ_MP (@lem1094866 A t h) (@lem1094865 A t h)). Qed.
Lemma lem1189677 {_27798 : Type'} (t : list _27798) (h : _27798) : (term217 _27798 h t) = h.
Proof. exact (@lem1189676 _27798 t h). Qed.
Lemma lem1189678 {_27798 : Type'} (t : list _27798) (h : _27798) : (term220 _27798 h t) = h.
Proof. exact (TRANS (@lem1189674 _27798 h t) (@lem1189677 _27798 t h)). Qed.
Lemma lem1189679 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem1189680 {_27796 _27797 _27798 : Type'} (t : list _27798) (f : type1518 _27796 _27797 _27798) (h : _27798) : (term221 _27796 _27797 _27798 f h t) = (f h).
Proof. exact (MK_COMB (@lem1189679 _27796 _27797 _27798 f) (@lem1189678 _27798 t h)). Qed.
Lemma lem1189682 {_25569 : Type'} (l : list _25569) : (term210 _25569 l) = (@hd _25569 l).
Proof. exact (EQ_MP (@lem1105742 _25569 l) (@lem1105741 _25569 l)). Qed.
Lemma lem1189683 {_27797 : Type'} (l : list _27797) : (term210 _27797 l) = (@hd _27797 l).
Proof. exact (@lem1189682 _27797 l). Qed.
Lemma lem1189684 {_27797 : Type'} (h' : _27797) (t' : list _27797) : (term220 _27797 h' t') = (term217 _27797 h' t').
Proof. exact (@lem1189683 _27797 (@cons _27797 h' t')). Qed.
Lemma lem1189686 {A : Type'} (t : list A) (h : A) : (term217 A h t) = h.
Proof. exact (EQ_MP (@lem1094866 A t h) (@lem1094865 A t h)). Qed.
Lemma lem1189687 {_27797 : Type'} (t : list _27797) (h : _27797) : (term217 _27797 h t) = h.
Proof. exact (@lem1189686 _27797 t h). Qed.
Lemma lem1189688 {_27797 : Type'} (t' : list _27797) (h' : _27797) : (term217 _27797 h' t') = h'.
Proof. exact (@lem1189687 _27797 t' h'). Qed.
Lemma lem1189689 {_27797 : Type'} (t' : list _27797) (h' : _27797) : (term220 _27797 h' t') = h'.
Proof. exact (TRANS (@lem1189684 _27797 h' t') (@lem1189688 _27797 t' h')). Qed.
Lemma lem1189690 {_27796 _27797 _27798 : Type'} (t : list _27798) (t' : list _27797) (f : type1518 _27796 _27797 _27798) (h : _27798) (h' : _27797) : (term203 _27796 _27797 _27798 f h t h' t') = (f h h').
Proof. exact (MK_COMB (@lem1189680 _27796 _27797 _27798 t f h) (@lem1189689 _27797 t' h')). Qed.
Lemma lem1189691 {_27796 _27797 _27798 : Type'} (t : list _27798) (t' : list _27797) (f : type1518 _27796 _27797 _27798) (h : _27798) (h' : _27797) : ((term202 _27796 _27797 _27798 f h t h' t') = (term203 _27796 _27797 _27798 f h t h' t')) = ((f h h') = (f h h')).
Proof. exact (MK_COMB (@lem1189670 _27796 _27797 _27798 t t' f h h') (@lem1189690 _27796 _27797 _27798 t t' f h h')). Qed.
Lemma lem1189693 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1189694 {_27796 : Type'} (x : _27796) : (x = x) = True.
Proof. exact (@lem1189693 _27796 x). Qed.
Lemma lem1189695 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (h : _27798) (h' : _27797) : ((f h h') = (f h h')) = True.
Proof. exact (@lem1189694 _27796 (f h h')). Qed.
Lemma lem1189696 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (h : _27798) (t : list _27798) (h' : _27797) (t' : list _27797) : ((term202 _27796 _27797 _27798 f h t h' t') = (term203 _27796 _27797 _27798 f h t h' t')) = True.
Proof. exact (TRANS (@lem1189691 _27796 _27797 _27798 t t' f h h') (@lem1189695 _27796 _27797 _27798 f h h')). Qed.
Lemma lem1189697 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (h : _27798) (t : list _27798) (h' : _27797) (t' : list _27797) : term222 _27796 _27797 _27798 f h t h' t'.
Proof. exact (fun h0 : term201 _27797 _27798 t t' => @lem1189696 _27796 _27797 _27798 f h t h' t'). Qed.
Lemma lem1189698 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (h : _27798) (h' : _27797) (t : list _27798) (t' : list _27797) : term223 _27796 _27797 _27798 f h h' t t'.
Proof. exact (@lem1189643 _27796 _27797 _27798 f h h' t t' True). Qed.
Lemma lem1189699 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (h : _27798) (h' : _27797) (t : list _27798) (t' : list _27797) : (term179 _27796 _27797 _27798 f h t h' t') = (term224 _27797 _27798 t t').
Proof. exact (@lem1189698 _27796 _27797 _27798 f h h' t t' (@lem1189697 _27796 _27797 _27798 f h t h' t')). Qed.
Lemma lem1189701 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem1189702 {_27797 _27798 : Type'} (t : list _27798) (t' : list _27797) : (term224 _27797 _27798 t t') = True.
Proof. exact (@lem1189701 (term201 _27797 _27798 t t')). Qed.
Lemma lem1189703 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (h : _27798) (t : list _27798) (h' : _27797) (t' : list _27797) : (term179 _27796 _27797 _27798 f h t h' t') = True.
Proof. exact (TRANS (@lem1189699 _27796 _27797 _27798 f h h' t t') (@lem1189702 _27797 _27798 t t')). Qed.
Lemma lem1189704 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (h : _27798) (t : list _27798) (h' : _27797) (t' : list _27797) : True = (term179 _27796 _27797 _27798 f h t h' t').
Proof. exact (SYM (@lem1189703 _27796 _27797 _27798 f h t h' t')). Qed.
Lemma lem1189705 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (h : _27798) (t : list _27798) (h' : _27797) (t' : list _27797) : term179 _27796 _27797 _27798 f h t h' t'.
Proof. exact (EQ_MP (@lem1189704 _27796 _27797 _27798 f h t h' t') (@lem0)). Qed.
Lemma lem1189706 (m : nat) : term225 m.
Proof. exact (@lem91415 m). Qed.
Lemma lem1189707 (m : nat) : (term225 m) = (term226 m).
Proof. exact (eq_refl (term225 m)). Qed.
Lemma lem1189708 (m : nat) : term226 m.
Proof. exact (EQ_MP (@lem1189707 m) (@lem1189706 m)). Qed.
Lemma lem1189709 (m : nat) (n : nat) : term227 m n.
Proof. exact (@lem1189708 m n). Qed.
Lemma lem1189710 (m : nat) (n : nat) : (term227 m n) = ((term228 m n) = (Peano.lt m n)).
Proof. exact (eq_refl (term227 m n)). Qed.
Lemma lem1189724 {_27796 _27797 _27798 : Type'} (m : list _27797) (f : type1518 _27796 _27797 _27798) (t : list _27798) (h1 : term9 _27796 _27797 _27798 f t) : term229 _27796 _27797 _27798 f t m.
Proof. exact (@lem1189052 _27796 _27797 _27798 f t h1 m). Qed.
Lemma lem1189725 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (t : list _27798) (m : list _27797) : (term229 _27796 _27797 _27798 f t m) = (term230 _27796 _27797 _27798 f t m).
Proof. exact (eq_refl (term229 _27796 _27797 _27798 f t m)). Qed.
Lemma lem1189726 {_27796 _27797 _27798 : Type'} (m : list _27797) (f : type1518 _27796 _27797 _27798) (t : list _27798) (h1 : term9 _27796 _27797 _27798 f t) : term230 _27796 _27797 _27798 f t m.
Proof. exact (EQ_MP (@lem1189725 _27796 _27797 _27798 f t m) (@lem1189724 _27796 _27797 _27798 m f t h1)). Qed.
Lemma lem1189727 {_27796 _27797 _27798 : Type'} (m : list _27797) (k : nat) (f : type1518 _27796 _27797 _27798) (t : list _27798) (h1 : term9 _27796 _27797 _27798 f t) : term231 _27796 _27797 _27798 f t m k.
Proof. exact (@lem1189726 _27796 _27797 _27798 m f t h1 k). Qed.
Lemma lem1189728 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (t : list _27798) (k : nat) (m : list _27797) : (term231 _27796 _27797 _27798 f t m k) = (term232 _27796 _27797 _27798 f t k m).
Proof. exact (eq_refl (term231 _27796 _27797 _27798 f t m k)). Qed.
Lemma lem1189729 {_27796 _27797 _27798 : Type'} (k : nat) (m : list _27797) (f : type1518 _27796 _27797 _27798) (t : list _27798) (h1 : term9 _27796 _27797 _27798 f t) : term232 _27796 _27797 _27798 f t k m.
Proof. exact (EQ_MP (@lem1189728 _27796 _27797 _27798 f t k m) (@lem1189727 _27796 _27797 _27798 m k f t h1)). Qed.
Lemma lem1189730 {_27797 _27798 : Type'} (t : list _27798) (k : nat) (m : list _27797) (h1 : term233 _27797 _27798 t k m) : term233 _27797 _27798 t k m.
Proof. exact (h1). Qed.
Lemma lem1189731 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (t : list _27798) (k : nat) (m : list _27797) (h1 : term9 _27796 _27797 _27798 f t) (h2 : term233 _27797 _27798 t k m) : (term234 _27796 _27797 _27798 k f t m) = (term235 _27796 _27797 _27798 f t k m).
Proof. exact (@lem1189729 _27796 _27797 _27798 k m f t h1 (@lem1189730 _27797 _27798 t k m h2)). Qed.
Lemma lem1189757 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term92 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem1189758 (p : Prop) (q : Prop) (p' : Prop) : term93 p q p'.
Proof. exact (fun q' : Prop => @lem1189757 p q p' q'). Qed.
Lemma lem1189759 (p : Prop) (q : Prop) : term94 p q.
Proof. exact (fun p' : Prop => @lem1189758 p q p'). Qed.
Lemma lem1189760 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (h : _27798) (t : list _27798) (k : nat) (h' : _27797) (t' : list _27797) : term236 _27796 _27797 _27798 f h t k h' t'.
Proof. exact (@lem1189759 (term237 _27797 _27798 t k t') ((term238 _27796 _27797 _27798 k f h t h' t') = (term239 _27796 _27797 _27798 f h t k h' t'))). Qed.
Lemma lem1189761 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (h : _27798) (t : list _27798) (k : nat) (h' : _27797) (t' : list _27797) (p' : Prop) : term240 _27796 _27797 _27798 f h t k h' t' p'.
Proof. exact (@lem1189760 _27796 _27797 _27798 f h t k h' t' p'). Qed.
Lemma lem1189762 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (h : _27798) (t : list _27798) (k : nat) (h' : _27797) (t' : list _27797) (p' : Prop) : (term240 _27796 _27797 _27798 f h t k h' t' p') = (term241 _27796 _27797 _27798 f h t k h' t' p').
Proof. exact (eq_refl (term240 _27796 _27797 _27798 f h t k h' t' p')). Qed.
Lemma lem1189763 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (h : _27798) (t : list _27798) (k : nat) (h' : _27797) (t' : list _27797) (p' : Prop) : term241 _27796 _27797 _27798 f h t k h' t' p'.
Proof. exact (EQ_MP (@lem1189762 _27796 _27797 _27798 f h t k h' t' p') (@lem1189761 _27796 _27797 _27798 f h t k h' t' p')). Qed.
Lemma lem1189764 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (h : _27798) (t : list _27798) (k : nat) (h' : _27797) (t' : list _27797) (p' : Prop) (q' : Prop) : term242 _27796 _27797 _27798 f h t k h' t' p' q'.
Proof. exact (@lem1189763 _27796 _27797 _27798 f h t k h' t' p' q'). Qed.
Lemma lem1189765 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (h : _27798) (t : list _27798) (k : nat) (h' : _27797) (t' : list _27797) (p' : Prop) (q' : Prop) : (term242 _27796 _27797 _27798 f h t k h' t' p' q') = (term243 _27796 _27797 _27798 f h t k h' t' p' q').
Proof. exact (eq_refl (term242 _27796 _27797 _27798 f h t k h' t' p' q')). Qed.
Lemma lem1189766 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (h : _27798) (t : list _27798) (k : nat) (h' : _27797) (t' : list _27797) (p' : Prop) (q' : Prop) : term243 _27796 _27797 _27798 f h t k h' t' p' q'.
Proof. exact (EQ_MP (@lem1189765 _27796 _27797 _27798 f h t k h' t' p' q') (@lem1189764 _27796 _27797 _27798 f h t k h' t' p' q')). Qed.
Lemma lem1189770 (m : nat) (n : nat) : (term228 m n) = (Peano.lt m n).
Proof. exact (EQ_MP (@lem1189710 m n) (@lem1189709 m n)). Qed.
Lemma lem1189771 {_27798 : Type'} (k : nat) (t : list _27798) : (term244 _27798 k t) = (term245 _27798 k t).
Proof. exact (@lem1189770 k (@List.length _27798 t)). Qed.
Lemma lem1189772 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1189773 {_27798 : Type'} (k : nat) (t : list _27798) : (term246 _27798 k t) = (term247 _27798 k t).
Proof. exact (MK_COMB (@lem1189772) (@lem1189771 _27798 k t)). Qed.
Lemma lem1189775 (m : nat) (n : nat) : (term228 m n) = (Peano.lt m n).
Proof. exact (EQ_MP (@lem1189710 m n) (@lem1189709 m n)). Qed.
Lemma lem1189776 {_27797 : Type'} (k : nat) (t' : list _27797) : (term244 _27797 k t') = (term245 _27797 k t').
Proof. exact (@lem1189775 k (@List.length _27797 t')). Qed.
Lemma lem1189777 {_27797 _27798 : Type'} (t : list _27798) (k : nat) (t' : list _27797) : (term237 _27797 _27798 t k t') = (term233 _27797 _27798 t k t').
Proof. exact (MK_COMB (@lem1189773 _27798 k t) (@lem1189776 _27797 k t')). Qed.
Lemma lem1189780 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (h : _27798) (h' : _27797) (t : list _27798) (k : nat) (t' : list _27797) (q' : Prop) : term248 _27796 _27797 _27798 f h h' t k t' q'.
Proof. exact (@lem1189766 _27796 _27797 _27798 f h t k h' t' (term233 _27797 _27798 t k t') q'). Qed.
Lemma lem1189781 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (h : _27798) (h' : _27797) (t : list _27798) (k : nat) (t' : list _27797) (q' : Prop) : term249 _27796 _27797 _27798 f h h' t k t' q'.
Proof. exact (@lem1189780 _27796 _27797 _27798 f h h' t k t' q' (@lem1189777 _27797 _27798 t k t')). Qed.
Lemma lem1189782 {_27797 _27798 : Type'} (t : list _27798) (k : nat) (t' : list _27797) (h1 : term233 _27797 _27798 t k t') : term233 _27797 _27798 t k t'.
Proof. exact (h1). Qed.
Lemma lem1189783 {_27797 _27798 : Type'} (t : list _27798) (k : nat) (t' : list _27797) (h1 : term233 _27797 _27798 t k t') : term245 _27797 k t'.
Proof. exact (proj2 (@lem1189782 _27797 _27798 t k t' h1)). Qed.
Lemma lem1189784 {_27797 : Type'} (k : nat) (t' : list _27797) : (term245 _27797 k t') = ((term245 _27797 k t') = True).
Proof. exact (@lem7 (term245 _27797 k t')). Qed.
Lemma lem1189786 {_27797 _27798 : Type'} (t : list _27798) (k : nat) (t' : list _27797) (h1 : term233 _27797 _27798 t k t') : term245 _27798 k t.
Proof. exact (proj1 (@lem1189782 _27797 _27798 t k t' h1)). Qed.
Lemma lem1189787 {_27798 : Type'} (k : nat) (t : list _27798) : (term245 _27798 k t) = ((term245 _27798 k t) = True).
Proof. exact (@lem7 (term245 _27798 k t)). Qed.
Lemma lem1189792 {_25569 : Type'} (n : nat) (l : list _25569) : (term250 _25569 n l) = (term251 _25569 n l).
Proof. exact (EQ_MP (@lem1105748 _25569 n l) (@lem1105747 _25569 n l)). Qed.
Lemma lem1189793 {_27796 : Type'} (n : nat) (l : list _27796) : (term250 _27796 n l) = (term251 _27796 n l).
Proof. exact (@lem1189792 _27796 n l). Qed.
Lemma lem1189794 {_27796 _27797 _27798 : Type'} (k : nat) (f : type1518 _27796 _27797 _27798) (h : _27798) (t : list _27798) (h' : _27797) (t' : list _27797) : (term238 _27796 _27797 _27798 k f h t h' t') = (term252 _27796 _27797 _27798 k f h t h' t').
Proof. exact (@lem1189793 _27796 k (term212 _27796 _27797 _27798 f h t h' t')). Qed.
Lemma lem1189796 {_25542 _25543 _25549 : Type'} (h1' : _25543) (h2' : _25542) (f : type1469 _25542 _25543 _25549) (t1 : list _25543) (t2 : list _25542) : (term213 _25542 _25543 _25549 f h1' t1 h2' t2) = (term214 _25542 _25543 _25549 h1' h2' f t1 t2).
Proof. exact (proj2 (@lem1105126 _25542 _25543 _25549 h1' h2' f t1 t2)). Qed.
Lemma lem1189797 {_27796 _27797 _27798 : Type'} (h1' : _27798) (h2' : _27797) (f : type1518 _27796 _27797 _27798) (t1 : list _27798) (t2 : list _27797) : (term212 _27796 _27797 _27798 f h1' t1 h2' t2) = (term215 _27796 _27797 _27798 h1' h2' f t1 t2).
Proof. exact (@lem1189796 _27797 _27798 _27796 h1' h2' f t1 t2). Qed.
Lemma lem1189798 {_27796 _27797 _27798 : Type'} (h : _27798) (h' : _27797) (f : type1518 _27796 _27797 _27798) (t : list _27798) (t' : list _27797) : (term212 _27796 _27797 _27798 f h t h' t') = (term215 _27796 _27797 _27798 h h' f t t').
Proof. exact (@lem1189797 _27796 _27797 _27798 h h' f t t'). Qed.
Lemma lem1189799 {_27796 : Type'} : (@tl _27796) = (@tl _27796).
Proof. exact (eq_refl (@tl _27796)). Qed.
Lemma lem1189800 {_27796 _27797 _27798 : Type'} (h : _27798) (h' : _27797) (f : type1518 _27796 _27797 _27798) (t : list _27798) (t' : list _27797) : (term253 _27796 _27797 _27798 f h t h' t') = (term254 _27796 _27797 _27798 h h' f t t').
Proof. exact (MK_COMB (@lem1189799 _27796) (@lem1189798 _27796 _27797 _27798 h h' f t t')). Qed.
Lemma lem1189802 {A : Type'} (h : A) (t : list A) : (term255 A h t) = t.
Proof. exact (EQ_MP (@lem1095389 A h t) (@lem1095388 A h t)). Qed.
Lemma lem1189803 {_27796 : Type'} (h : _27796) (t : list _27796) : (term255 _27796 h t) = t.
Proof. exact (@lem1189802 _27796 h t). Qed.
Lemma lem1189804 {_27796 _27797 _27798 : Type'} (h : _27798) (h' : _27797) (f : type1518 _27796 _27797 _27798) (t : list _27798) (t' : list _27797) : (term254 _27796 _27797 _27798 h h' f t t') = (@MAP2 _27796 _27798 _27797 f t t').
Proof. exact (@lem1189803 _27796 (f h h') (@MAP2 _27796 _27798 _27797 f t t')). Qed.
Lemma lem1189805 {_27796 _27797 _27798 : Type'} (h : _27798) (h' : _27797) (f : type1518 _27796 _27797 _27798) (t : list _27798) (t' : list _27797) : (term253 _27796 _27797 _27798 f h t h' t') = (@MAP2 _27796 _27798 _27797 f t t').
Proof. exact (TRANS (@lem1189800 _27796 _27797 _27798 h h' f t t') (@lem1189804 _27796 _27797 _27798 h h' f t t')). Qed.
Lemma lem1189806 {_27796 : Type'} (k : nat) : (@EL _27796 k) = (@EL _27796 k).
Proof. exact (eq_refl (@EL _27796 k)). Qed.
Lemma lem1189807 {_27796 _27797 _27798 : Type'} (h : _27798) (h' : _27797) (k : nat) (f : type1518 _27796 _27797 _27798) (t : list _27798) (t' : list _27797) : (term252 _27796 _27797 _27798 k f h t h' t') = (term234 _27796 _27797 _27798 k f t t').
Proof. exact (MK_COMB (@lem1189806 _27796 k) (@lem1189805 _27796 _27797 _27798 h h' f t t')). Qed.
Lemma lem1189809 {_27796 _27797 _27798 : Type'} (k : nat) (m : list _27797) (f : type1518 _27796 _27797 _27798) (t : list _27798) (h1 : term9 _27796 _27797 _27798 f t) : term232 _27796 _27797 _27798 f t k m.
Proof. exact (fun h0 : term233 _27797 _27798 t k m => @lem1189731 _27796 _27797 _27798 f t k m h1 h0). Qed.
Lemma lem1189810 {_27796 _27797 _27798 : Type'} (k : nat) (m : list _27797) (f : type1518 _27796 _27797 _27798) (t : list _27798) (h1 : term9 _27796 _27797 _27798 f t) : term232 _27796 _27797 _27798 f t k m.
Proof. exact (@lem1189809 _27796 _27797 _27798 k m f t h1). Qed.
Lemma lem1189811 {_27796 _27797 _27798 : Type'} (k : nat) (t' : list _27797) (f : type1518 _27796 _27797 _27798) (t : list _27798) (h1 : term9 _27796 _27797 _27798 f t) : term232 _27796 _27797 _27798 f t k t'.
Proof. exact (@lem1189810 _27796 _27797 _27798 k t' f t h1). Qed.
Lemma lem1189815 {_27797 _27798 : Type'} (t : list _27798) (k : nat) (t' : list _27797) (h1 : term233 _27797 _27798 t k t') : (term245 _27798 k t) = True.
Proof. exact (EQ_MP (@lem1189787 _27798 k t) (@lem1189786 _27797 _27798 t k t' h1)). Qed.
Lemma lem1189816 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1189817 {_27797 _27798 : Type'} (t : list _27798) (k : nat) (t' : list _27797) (h1 : term233 _27797 _27798 t k t') : (term247 _27798 k t) = (and True).
Proof. exact (MK_COMB (@lem1189816) (@lem1189815 _27797 _27798 t k t' h1)). Qed.
Lemma lem1189819 {_27797 _27798 : Type'} (t : list _27798) (k : nat) (t' : list _27797) (h1 : term233 _27797 _27798 t k t') : (term245 _27797 k t') = True.
Proof. exact (EQ_MP (@lem1189784 _27797 k t') (@lem1189783 _27797 _27798 t k t' h1)). Qed.
Lemma lem1189820 {_27797 _27798 : Type'} (t : list _27798) (k : nat) (t' : list _27797) (h1 : term233 _27797 _27798 t k t') : (term233 _27797 _27798 t k t') = (True /\ True).
Proof. exact (MK_COMB (@lem1189817 _27797 _27798 t k t' h1) (@lem1189819 _27797 _27798 t k t' h1)). Qed.
Lemma lem1189822 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1189823 : (True /\ True) = True.
Proof. exact (@lem1189822 True). Qed.
Lemma lem1189824 {_27797 _27798 : Type'} (t : list _27798) (k : nat) (t' : list _27797) (h1 : term233 _27797 _27798 t k t') : (term233 _27797 _27798 t k t') = True.
Proof. exact (TRANS (@lem1189820 _27797 _27798 t k t' h1) (@lem1189823)). Qed.
Lemma lem1189825 {_27797 _27798 : Type'} (t : list _27798) (k : nat) (t' : list _27797) (h1 : term233 _27797 _27798 t k t') : True = (term233 _27797 _27798 t k t').
Proof. exact (SYM (@lem1189824 _27797 _27798 t k t' h1)). Qed.
Lemma lem1189826 {_27797 _27798 : Type'} (t : list _27798) (k : nat) (t' : list _27797) (h1 : term233 _27797 _27798 t k t') : term233 _27797 _27798 t k t'.
Proof. exact (EQ_MP (@lem1189825 _27797 _27798 t k t' h1) (@lem0)). Qed.
Lemma lem1189827 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (t : list _27798) (k : nat) (t' : list _27797) (h1 : term9 _27796 _27797 _27798 f t) (h2 : term233 _27797 _27798 t k t') : (term234 _27796 _27797 _27798 k f t t') = (term235 _27796 _27797 _27798 f t k t').
Proof. exact (@lem1189811 _27796 _27797 _27798 k t' f t h1 (@lem1189826 _27797 _27798 t k t' h2)). Qed.
Lemma lem1189828 {_27796 _27797 _27798 : Type'} (h : _27798) (h' : _27797) (f : type1518 _27796 _27797 _27798) (t : list _27798) (k : nat) (t' : list _27797) (h1 : term9 _27796 _27797 _27798 f t) (h2 : term233 _27797 _27798 t k t') : (term252 _27796 _27797 _27798 k f h t h' t') = (term235 _27796 _27797 _27798 f t k t').
Proof. exact (TRANS (@lem1189807 _27796 _27797 _27798 h h' k f t t') (@lem1189827 _27796 _27797 _27798 f t k t' h1 h2)). Qed.
Lemma lem1189829 {_27796 _27797 _27798 : Type'} (h : _27798) (h' : _27797) (f : type1518 _27796 _27797 _27798) (t : list _27798) (k : nat) (t' : list _27797) (h1 : term9 _27796 _27797 _27798 f t) (h2 : term233 _27797 _27798 t k t') : (term238 _27796 _27797 _27798 k f h t h' t') = (term235 _27796 _27797 _27798 f t k t').
Proof. exact (TRANS (@lem1189794 _27796 _27797 _27798 k f h t h' t') (@lem1189828 _27796 _27797 _27798 h h' f t k t' h1 h2)). Qed.
Lemma lem1189830 {_27796 : Type'} : (@eq _27796) = (@eq _27796).
Proof. exact (eq_refl (@eq _27796)). Qed.
Lemma lem1189831 {_27796 _27797 _27798 : Type'} (h : _27798) (h' : _27797) (f : type1518 _27796 _27797 _27798) (t : list _27798) (k : nat) (t' : list _27797) (h1 : term9 _27796 _27797 _27798 f t) (h2 : term233 _27797 _27798 t k t') : (term256 _27796 _27797 _27798 k f h t h' t') = (term257 _27796 _27797 _27798 f t k t').
Proof. exact (MK_COMB (@lem1189830 _27796) (@lem1189829 _27796 _27797 _27798 h h' f t k t' h1 h2)). Qed.
Lemma lem1189833 {_25569 : Type'} (n : nat) (l : list _25569) : (term250 _25569 n l) = (term251 _25569 n l).
Proof. exact (EQ_MP (@lem1105748 _25569 n l) (@lem1105747 _25569 n l)). Qed.
Lemma lem1189834 {_27798 : Type'} (n : nat) (l : list _27798) : (term250 _27798 n l) = (term251 _27798 n l).
Proof. exact (@lem1189833 _27798 n l). Qed.
Lemma lem1189835 {_27798 : Type'} (k : nat) (h : _27798) (t : list _27798) : (term258 _27798 k h t) = (term259 _27798 k h t).
Proof. exact (@lem1189834 _27798 k (@cons _27798 h t)). Qed.
Lemma lem1189837 {A : Type'} (h : A) (t : list A) : (term255 A h t) = t.
Proof. exact (EQ_MP (@lem1095389 A h t) (@lem1095388 A h t)). Qed.
Lemma lem1189838 {_27798 : Type'} (h : _27798) (t : list _27798) : (term255 _27798 h t) = t.
Proof. exact (@lem1189837 _27798 h t). Qed.
Lemma lem1189839 {_27798 : Type'} (k : nat) : (@EL _27798 k) = (@EL _27798 k).
Proof. exact (eq_refl (@EL _27798 k)). Qed.
Lemma lem1189840 {_27798 : Type'} (h : _27798) (k : nat) (t : list _27798) : (term259 _27798 k h t) = (@EL _27798 k t).
Proof. exact (MK_COMB (@lem1189839 _27798 k) (@lem1189838 _27798 h t)). Qed.
Lemma lem1189841 {_27798 : Type'} (h : _27798) (k : nat) (t : list _27798) : (term258 _27798 k h t) = (@EL _27798 k t).
Proof. exact (TRANS (@lem1189835 _27798 k h t) (@lem1189840 _27798 h k t)). Qed.
Lemma lem1189842 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem1189843 {_27796 _27797 _27798 : Type'} (h : _27798) (f : type1518 _27796 _27797 _27798) (k : nat) (t : list _27798) : (term260 _27796 _27797 _27798 f k h t) = (term261 _27796 _27797 _27798 f k t).
Proof. exact (MK_COMB (@lem1189842 _27796 _27797 _27798 f) (@lem1189841 _27798 h k t)). Qed.
Lemma lem1189845 {_25569 : Type'} (n : nat) (l : list _25569) : (term250 _25569 n l) = (term251 _25569 n l).
Proof. exact (EQ_MP (@lem1105748 _25569 n l) (@lem1105747 _25569 n l)). Qed.
Lemma lem1189846 {_27797 : Type'} (n : nat) (l : list _27797) : (term250 _27797 n l) = (term251 _27797 n l).
Proof. exact (@lem1189845 _27797 n l). Qed.
Lemma lem1189847 {_27797 : Type'} (k : nat) (h' : _27797) (t' : list _27797) : (term258 _27797 k h' t') = (term259 _27797 k h' t').
Proof. exact (@lem1189846 _27797 k (@cons _27797 h' t')). Qed.
Lemma lem1189849 {A : Type'} (h : A) (t : list A) : (term255 A h t) = t.
Proof. exact (EQ_MP (@lem1095389 A h t) (@lem1095388 A h t)). Qed.
Lemma lem1189850 {_27797 : Type'} (h : _27797) (t : list _27797) : (term255 _27797 h t) = t.
Proof. exact (@lem1189849 _27797 h t). Qed.
Lemma lem1189851 {_27797 : Type'} (h' : _27797) (t' : list _27797) : (term255 _27797 h' t') = t'.
Proof. exact (@lem1189850 _27797 h' t'). Qed.
Lemma lem1189852 {_27797 : Type'} (k : nat) : (@EL _27797 k) = (@EL _27797 k).
Proof. exact (eq_refl (@EL _27797 k)). Qed.
Lemma lem1189853 {_27797 : Type'} (h' : _27797) (k : nat) (t' : list _27797) : (term259 _27797 k h' t') = (@EL _27797 k t').
Proof. exact (MK_COMB (@lem1189852 _27797 k) (@lem1189851 _27797 h' t')). Qed.
Lemma lem1189854 {_27797 : Type'} (h' : _27797) (k : nat) (t' : list _27797) : (term258 _27797 k h' t') = (@EL _27797 k t').
Proof. exact (TRANS (@lem1189847 _27797 k h' t') (@lem1189853 _27797 h' k t')). Qed.
Lemma lem1189855 {_27796 _27797 _27798 : Type'} (h : _27798) (h' : _27797) (f : type1518 _27796 _27797 _27798) (t : list _27798) (k : nat) (t' : list _27797) : (term239 _27796 _27797 _27798 f h t k h' t') = (term235 _27796 _27797 _27798 f t k t').
Proof. exact (MK_COMB (@lem1189843 _27796 _27797 _27798 h f k t) (@lem1189854 _27797 h' k t')). Qed.
Lemma lem1189856 {_27796 _27797 _27798 : Type'} (h : _27798) (h' : _27797) (f : type1518 _27796 _27797 _27798) (t : list _27798) (k : nat) (t' : list _27797) (h1 : term9 _27796 _27797 _27798 f t) (h2 : term233 _27797 _27798 t k t') : ((term238 _27796 _27797 _27798 k f h t h' t') = (term239 _27796 _27797 _27798 f h t k h' t')) = ((term235 _27796 _27797 _27798 f t k t') = (term235 _27796 _27797 _27798 f t k t')).
Proof. exact (MK_COMB (@lem1189831 _27796 _27797 _27798 h h' f t k t' h1 h2) (@lem1189855 _27796 _27797 _27798 h h' f t k t')). Qed.
Lemma lem1189858 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1189859 {_27796 : Type'} (x : _27796) : (x = x) = True.
Proof. exact (@lem1189858 _27796 x). Qed.
Lemma lem1189860 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (t : list _27798) (k : nat) (t' : list _27797) : ((term235 _27796 _27797 _27798 f t k t') = (term235 _27796 _27797 _27798 f t k t')) = True.
Proof. exact (@lem1189859 _27796 (term235 _27796 _27797 _27798 f t k t')). Qed.
Lemma lem1189861 {_27796 _27797 _27798 : Type'} (h : _27798) (h' : _27797) (f : type1518 _27796 _27797 _27798) (t : list _27798) (k : nat) (t' : list _27797) (h1 : term9 _27796 _27797 _27798 f t) (h2 : term233 _27797 _27798 t k t') : ((term238 _27796 _27797 _27798 k f h t h' t') = (term239 _27796 _27797 _27798 f h t k h' t')) = True.
Proof. exact (TRANS (@lem1189856 _27796 _27797 _27798 h h' f t k t' h1 h2) (@lem1189860 _27796 _27797 _27798 f t k t')). Qed.
Lemma lem1189862 {_27796 _27797 _27798 : Type'} (h : _27798) (k : nat) (h' : _27797) (t' : list _27797) (f : type1518 _27796 _27797 _27798) (t : list _27798) (h1 : term9 _27796 _27797 _27798 f t) : term262 _27796 _27797 _27798 f h t k h' t'.
Proof. exact (fun h0 : term233 _27797 _27798 t k t' => @lem1189861 _27796 _27797 _27798 h h' f t k t' h1 h0). Qed.
Lemma lem1189863 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (h : _27798) (h' : _27797) (t : list _27798) (k : nat) (t' : list _27797) : term263 _27796 _27797 _27798 f h h' t k t'.
Proof. exact (@lem1189781 _27796 _27797 _27798 f h h' t k t' True). Qed.
Lemma lem1189864 {_27796 _27797 _27798 : Type'} (h : _27798) (h' : _27797) (k : nat) (t' : list _27797) (f : type1518 _27796 _27797 _27798) (t : list _27798) (h1 : term9 _27796 _27797 _27798 f t) : (term186 _27796 _27797 _27798 f h t k h' t') = (term264 _27797 _27798 t k t').
Proof. exact (@lem1189863 _27796 _27797 _27798 f h h' t k t' (@lem1189862 _27796 _27797 _27798 h k h' t' f t h1)). Qed.
Lemma lem1189866 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem1189867 {_27797 _27798 : Type'} (t : list _27798) (k : nat) (t' : list _27797) : (term264 _27797 _27798 t k t') = True.
Proof. exact (@lem1189866 (term233 _27797 _27798 t k t')). Qed.
Lemma lem1189868 {_27796 _27797 _27798 : Type'} (h : _27798) (k : nat) (h' : _27797) (t' : list _27797) (f : type1518 _27796 _27797 _27798) (t : list _27798) (h1 : term9 _27796 _27797 _27798 f t) : (term186 _27796 _27797 _27798 f h t k h' t') = True.
Proof. exact (TRANS (@lem1189864 _27796 _27797 _27798 h h' k t' f t h1) (@lem1189867 _27797 _27798 t k t')). Qed.
Lemma lem1189869 {_27796 _27797 _27798 : Type'} (h : _27798) (k : nat) (h' : _27797) (t' : list _27797) (f : type1518 _27796 _27797 _27798) (t : list _27798) (h1 : term9 _27796 _27797 _27798 f t) : True = (term186 _27796 _27797 _27798 f h t k h' t').
Proof. exact (SYM (@lem1189868 _27796 _27797 _27798 h k h' t' f t h1)). Qed.
Lemma lem1189870 {_27796 _27797 _27798 : Type'} (h : _27798) (k : nat) (h' : _27797) (t' : list _27797) (f : type1518 _27796 _27797 _27798) (t : list _27798) (h1 : term9 _27796 _27797 _27798 f t) : term186 _27796 _27797 _27798 f h t k h' t'.
Proof. exact (EQ_MP (@lem1189869 _27796 _27797 _27798 h k h' t' f t h1) (@lem0)). Qed.
Lemma lem1189871 {_27796 _27797 _27798 : Type'} (h : _27798) (k : nat) (h' : _27797) (t' : list _27797) (f : type1518 _27796 _27797 _27798) (t : list _27798) (h1 : term9 _27796 _27797 _27798 f t) : term188 _27796 _27797 _27798 f h t k h' t'.
Proof. exact (fun h0 : term172 _27796 _27797 _27798 f h t k h' t' => @lem1189870 _27796 _27797 _27798 h k h' t' f t h1). Qed.
Lemma lem1189876 {_27796 _27797 _27798 : Type'} (h : _27798) (h' : _27797) (t' : list _27797) (f : type1518 _27796 _27797 _27798) (t : list _27798) (h1 : term9 _27796 _27797 _27798 f t) : term192 _27796 _27797 _27798 f h t h' t'.
Proof. exact (fun k : nat => @lem1189871 _27796 _27797 _27798 h k h' t' f t h1). Qed.
Lemma lem1189877 {_27796 _27797 _27798 : Type'} (h : _27798) (h' : _27797) (t' : list _27797) (f : type1518 _27796 _27797 _27798) (t : list _27798) (h1 : term9 _27796 _27797 _27798 f t) : term194 _27796 _27797 _27798 f h t h' t'.
Proof. exact (conj (@lem1189705 _27796 _27797 _27798 f h t h' t') (@lem1189876 _27796 _27797 _27798 h h' t' f t h1)). Qed.
Lemma lem1189878 {_27796 _27797 _27798 : Type'} (h : _27798) (h' : _27797) (t' : list _27797) (f : type1518 _27796 _27797 _27798) (t : list _27798) (h1 : term9 _27796 _27797 _27798 f t) : term175 _27796 _27797 _27798 f h t h' t'.
Proof. exact (@lem1189583 _27796 _27797 _27798 f h t h' t' (@lem1189877 _27796 _27797 _27798 h h' t' f t h1)). Qed.
Lemma lem1189879 {_27796 _27797 _27798 : Type'} (h : _27798) (h' : _27797) (t' : list _27797) (f : type1518 _27796 _27797 _27798) (t : list _27798) (h1 : term9 _27796 _27797 _27798 f t) : term72 _27796 _27797 _27798 f h t h' t'.
Proof. exact (EQ_MP (@lem1189560 _27796 _27797 _27798 f h t h' t') (@lem1189878 _27796 _27797 _27798 h h' t' f t h1)). Qed.
Lemma lem1189880 {_27796 _27797 _27798 : Type'} (h : _27798) (h' : _27797) (t' : list _27797) (f : type1518 _27796 _27797 _27798) (t : list _27798) (h1 : term9 _27796 _27797 _27798 f t) : term74 _27796 _27797 _27798 f h t h' t'.
Proof. exact (fun h0 : term68 _27796 _27797 _27798 f h t t' => @lem1189879 _27796 _27797 _27798 h h' t' f t h1). Qed.
Lemma lem1189885 {_27796 _27797 _27798 : Type'} (h : _27798) (h' : _27797) (f : type1518 _27796 _27797 _27798) (t : list _27798) (h1 : term9 _27796 _27797 _27798 f t) : term78 _27796 _27797 _27798 f h t h'.
Proof. exact (fun t' : list _27797 => @lem1189880 _27796 _27797 _27798 h h' t' f t h1). Qed.
Lemma lem1189890 {_27796 _27797 _27798 : Type'} (h : _27798) (f : type1518 _27796 _27797 _27798) (t : list _27798) (h1 : term9 _27796 _27797 _27798 f t) : term82 _27796 _27797 _27798 f h t.
Proof. exact (fun h' : _27797 => @lem1189885 _27796 _27797 _27798 h h' f t h1). Qed.
Lemma lem1189891 {_27796 _27797 _27798 : Type'} (h : _27798) (f : type1518 _27796 _27797 _27798) (t : list _27798) (h1 : term9 _27796 _27797 _27798 f t) : term84 _27796 _27797 _27798 f h t.
Proof. exact (conj (@lem1189363 _27796 _27797 _27798 f h t) (@lem1189890 _27796 _27797 _27798 h f t h1)). Qed.
Lemma lem1189892 {_27796 _27797 _27798 : Type'} (h : _27798) (f : type1518 _27796 _27797 _27798) (t : list _27798) (h1 : term9 _27796 _27797 _27798 f t) : term13 _27796 _27797 _27798 f h t.
Proof. exact (@lem1189107 _27796 _27797 _27798 f h t (@lem1189891 _27796 _27797 _27798 h f t h1)). Qed.
Lemma lem1189893 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (h : _27797) (t : list _27797) : term45 _27796 _27797 _27798 f h t.
Proof. exact (fun h0 : term39 _27796 _27797 _27798 f t => @lem1189274 _27796 _27797 _27798 f h t). Qed.
Lemma lem1189898 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (h : _27797) : term49 _27796 _27797 _27798 f h.
Proof. exact (fun t : list _27797 => @lem1189893 _27796 _27797 _27798 f h t). Qed.
Lemma lem1189903 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) : term53 _27796 _27797 _27798 f.
Proof. exact (fun h : _27797 => @lem1189898 _27796 _27797 _27798 f h). Qed.
Lemma lem1189904 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) : term55 _27796 _27797 _27798 f.
Proof. exact (conj (@lem1189188 _27796 _27797 _27798 f) (@lem1189903 _27796 _27797 _27798 f)). Qed.
Lemma lem1189905 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) : term5 _27796 _27797 _27798 f.
Proof. exact (@lem1189079 _27796 _27797 _27798 f (@lem1189904 _27796 _27797 _27798 f)). Qed.
Lemma lem1189906 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (h : _27798) (t : list _27798) : term15 _27796 _27797 _27798 f h t.
Proof. exact (fun h0 : term9 _27796 _27797 _27798 f t => @lem1189892 _27796 _27797 _27798 h f t h0). Qed.
Lemma lem1189911 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) (h : _27798) : term19 _27796 _27797 _27798 f h.
Proof. exact (fun t : list _27798 => @lem1189906 _27796 _27797 _27798 f h t). Qed.
Lemma lem1189916 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) : term23 _27796 _27797 _27798 f.
Proof. exact (fun h : _27798 => @lem1189911 _27796 _27797 _27798 f h). Qed.
Lemma lem1189917 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) : term25 _27796 _27797 _27798 f.
Proof. exact (conj (@lem1189905 _27796 _27797 _27798 f) (@lem1189916 _27796 _27797 _27798 f)). Qed.
Lemma lem1189918 {_27796 _27797 _27798 : Type'} (f : type1518 _27796 _27797 _27798) : term30 _27796 _27797 _27798 f.
Proof. exact (@lem1189051 _27796 _27797 _27798 f (@lem1189917 _27796 _27797 _27798 f)). Qed.
Lemma lem1189923 {_27796 _27797 _27798 : Type'} : term265 _27796 _27797 _27798.
Proof. exact (fun f : type1518 _27796 _27797 _27798 => @lem1189918 _27796 _27797 _27798 f). Qed.
