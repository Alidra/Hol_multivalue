Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm514290_term_abbrevs.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1842_spec.
Require Import thm1845_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm513551_spec.
Lemma lem513882 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem513883 (x : nat) : (x = x) = True.
Proof. exact (@lem513882 nat x). Qed.
Lemma lem513884 (m : nat) (n : nat) : ((Nat.add m n) = (Nat.add m n)) = True.
Proof. exact (@lem513883 (Nat.add m n)). Qed.
Lemma lem513885 (m : nat) : (term0 m) = term1.
Proof. exact (fun_ext (fun n : nat => @lem513884 m n)). Qed.
Lemma lem513886 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem513887 (m : nat) : (term2 m) = term3.
Proof. exact (MK_COMB (@lem513886) (@lem513885 m)). Qed.
Lemma lem513889 {A : Type'} (t : Prop) : (term4 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem513890 (t : Prop) : (term5 t) = t.
Proof. exact (@lem513889 nat t). Qed.
Lemma lem513891 : term3 = True.
Proof. exact (@lem513890 True). Qed.
Lemma lem513892 (m : nat) : (term2 m) = True.
Proof. exact (TRANS (@lem513887 m) (@lem513891)). Qed.
Lemma lem513893 : term6 = term1.
Proof. exact (fun_ext (fun m : nat => @lem513892 m)). Qed.
Lemma lem513894 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem513895 : term7 = term3.
Proof. exact (MK_COMB (@lem513894) (@lem513893)). Qed.
Lemma lem513897 {A : Type'} (t : Prop) : (term4 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem513898 (t : Prop) : (term5 t) = t.
Proof. exact (@lem513897 nat t). Qed.
Lemma lem513899 : term3 = True.
Proof. exact (@lem513898 True). Qed.
Lemma lem513900 : term7 = True.
Proof. exact (TRANS (@lem513895) (@lem513899)). Qed.
Lemma lem513901 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem513902 : term8 = (and True).
Proof. exact (MK_COMB (@lem513901) (@lem513900)). Qed.
Lemma lem513906 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem513907 (x : nat) : (x = x) = True.
Proof. exact (@lem513906 nat x). Qed.
Lemma lem513908 : (0 = 0) = True.
Proof. exact (@lem513907 0). Qed.
Lemma lem513909 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem513910 : term9 = (and True).
Proof. exact (MK_COMB (@lem513909) (@lem513908)). Qed.
Lemma lem513918 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem513919 (x : nat) : (x = x) = True.
Proof. exact (@lem513918 nat x). Qed.
Lemma lem513920 (n : nat) : ((Nat.add n n) = (Nat.add n n)) = True.
Proof. exact (@lem513919 (Nat.add n n)). Qed.
Lemma lem513921 : term10 = term1.
Proof. exact (fun_ext (fun n : nat => @lem513920 n)). Qed.
Lemma lem513922 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem513923 : term11 = term3.
Proof. exact (MK_COMB (@lem513922) (@lem513921)). Qed.
Lemma lem513925 {A : Type'} (t : Prop) : (term4 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem513926 (t : Prop) : (term5 t) = t.
Proof. exact (@lem513925 nat t). Qed.
Lemma lem513927 : term3 = True.
Proof. exact (@lem513926 True). Qed.
Lemma lem513928 : term11 = True.
Proof. exact (TRANS (@lem513923) (@lem513927)). Qed.
Lemma lem513929 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem513930 : term12 = (and True).
Proof. exact (MK_COMB (@lem513929) (@lem513928)). Qed.
Lemma lem513938 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem513939 (x : nat) : (x = x) = True.
Proof. exact (@lem513938 nat x). Qed.
Lemma lem513940 (n : nat) : ((Nat.add n n) = (Nat.add n n)) = True.
Proof. exact (@lem513939 (Nat.add n n)). Qed.
Lemma lem513941 : term10 = term1.
Proof. exact (fun_ext (fun n : nat => @lem513940 n)). Qed.
Lemma lem513942 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem513943 : term11 = term3.
Proof. exact (MK_COMB (@lem513942) (@lem513941)). Qed.
Lemma lem513945 {A : Type'} (t : Prop) : (term4 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem513946 (t : Prop) : (term5 t) = t.
Proof. exact (@lem513945 nat t). Qed.
Lemma lem513947 : term3 = True.
Proof. exact (@lem513946 True). Qed.
Lemma lem513948 : term11 = True.
Proof. exact (TRANS (@lem513943) (@lem513947)). Qed.
Lemma lem513949 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem513950 : term12 = (and True).
Proof. exact (MK_COMB (@lem513949) (@lem513948)). Qed.
Lemma lem513958 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem513959 (x : nat) : (x = x) = True.
Proof. exact (@lem513958 nat x). Qed.
Lemma lem513960 (n : nat) : ((Nat.add n n) = (Nat.add n n)) = True.
Proof. exact (@lem513959 (Nat.add n n)). Qed.
Lemma lem513961 : term10 = term1.
Proof. exact (fun_ext (fun n : nat => @lem513960 n)). Qed.
Lemma lem513962 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem513963 : term11 = term3.
Proof. exact (MK_COMB (@lem513962) (@lem513961)). Qed.
Lemma lem513965 {A : Type'} (t : Prop) : (term4 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem513966 (t : Prop) : (term5 t) = t.
Proof. exact (@lem513965 nat t). Qed.
Lemma lem513967 : term3 = True.
Proof. exact (@lem513966 True). Qed.
Lemma lem513968 : term11 = True.
Proof. exact (TRANS (@lem513963) (@lem513967)). Qed.
Lemma lem513969 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem513970 : term12 = (and True).
Proof. exact (MK_COMB (@lem513969) (@lem513968)). Qed.
Lemma lem513978 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem513979 (x : nat) : (x = x) = True.
Proof. exact (@lem513978 nat x). Qed.
Lemma lem513980 (n : nat) : ((Nat.add n n) = (Nat.add n n)) = True.
Proof. exact (@lem513979 (Nat.add n n)). Qed.
Lemma lem513981 : term10 = term1.
Proof. exact (fun_ext (fun n : nat => @lem513980 n)). Qed.
Lemma lem513982 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem513983 : term11 = term3.
Proof. exact (MK_COMB (@lem513982) (@lem513981)). Qed.
Lemma lem513985 {A : Type'} (t : Prop) : (term4 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem513986 (t : Prop) : (term5 t) = t.
Proof. exact (@lem513985 nat t). Qed.
Lemma lem513987 : term3 = True.
Proof. exact (@lem513986 True). Qed.
Lemma lem513988 : term11 = True.
Proof. exact (TRANS (@lem513983) (@lem513987)). Qed.
Lemma lem513989 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem513990 : term12 = (and True).
Proof. exact (MK_COMB (@lem513989) (@lem513988)). Qed.
Lemma lem514004 (m : nat) (n : nat) (p : nat) : (term13 m n p) = (term14 m n p).
Proof. exact (proj1 (@lem513551 n m p)). Qed.
Lemma lem514005 (m : nat) (n : nat) : (term15 m n) = (term16 m n).
Proof. exact (@lem514004 m m (Nat.add n n)). Qed.
Lemma lem514021 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem514022 (m : nat) (n : nat) : (term17 m n) = (term18 m n).
Proof. exact (MK_COMB (@lem514021) (@lem514005 m n)). Qed.
Lemma lem514024 (m : nat) (n : nat) (p : nat) : (term13 m n p) = (term14 m n p).
Proof. exact (proj1 (@lem513551 n m p)). Qed.
Lemma lem514025 (m : nat) (n : nat) : (term19 m n) = (term20 m n).
Proof. exact (@lem514024 m n (Nat.add m n)). Qed.
Lemma lem514033 (n : nat) (m : nat) (p : nat) : (term14 m n p) = (term14 n m p).
Proof. exact (proj2 (@lem513551 n m p)). Qed.
Lemma lem514034 (m : nat) (n : nat) : (term21 m n) = (term22 m n).
Proof. exact (@lem514033 m n n). Qed.
Lemma lem514044 (m : nat) : (Nat.add m) = (Nat.add m).
Proof. exact (eq_refl (Nat.add m)). Qed.
Lemma lem514045 (m : nat) (n : nat) : (term20 m n) = (term16 m n).
Proof. exact (MK_COMB (@lem514044 m) (@lem514034 m n)). Qed.
Lemma lem514052 (m : nat) (n : nat) : (term19 m n) = (term16 m n).
Proof. exact (TRANS (@lem514025 m n) (@lem514045 m n)). Qed.
Lemma lem514053 (m : nat) (n : nat) : ((term15 m n) = (term19 m n)) = ((term16 m n) = (term16 m n)).
Proof. exact (MK_COMB (@lem514022 m n) (@lem514052 m n)). Qed.
Lemma lem514055 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem514056 (x : nat) : (x = x) = True.
Proof. exact (@lem514055 nat x). Qed.
Lemma lem514057 (m : nat) (n : nat) : ((term16 m n) = (term16 m n)) = True.
Proof. exact (@lem514056 (term16 m n)). Qed.
Lemma lem514058 (m : nat) (n : nat) : ((term15 m n) = (term19 m n)) = True.
Proof. exact (TRANS (@lem514053 m n) (@lem514057 m n)). Qed.
Lemma lem514059 (m : nat) : (term23 m) = term1.
Proof. exact (fun_ext (fun n : nat => @lem514058 m n)). Qed.
Lemma lem514060 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem514061 (m : nat) : (term24 m) = term3.
Proof. exact (MK_COMB (@lem514060) (@lem514059 m)). Qed.
Lemma lem514063 {A : Type'} (t : Prop) : (term4 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem514064 (t : Prop) : (term5 t) = t.
Proof. exact (@lem514063 nat t). Qed.
Lemma lem514065 : term3 = True.
Proof. exact (@lem514064 True). Qed.
Lemma lem514066 (m : nat) : (term24 m) = True.
Proof. exact (TRANS (@lem514061 m) (@lem514065)). Qed.
Lemma lem514067 : term25 = term1.
Proof. exact (fun_ext (fun m : nat => @lem514066 m)). Qed.
Lemma lem514068 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem514069 : term26 = term3.
Proof. exact (MK_COMB (@lem514068) (@lem514067)). Qed.
Lemma lem514071 {A : Type'} (t : Prop) : (term4 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem514072 (t : Prop) : (term5 t) = t.
Proof. exact (@lem514071 nat t). Qed.
Lemma lem514073 : term3 = True.
Proof. exact (@lem514072 True). Qed.
Lemma lem514074 : term26 = True.
Proof. exact (TRANS (@lem514069) (@lem514073)). Qed.
Lemma lem514075 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem514076 : term27 = (and True).
Proof. exact (MK_COMB (@lem514075) (@lem514074)). Qed.
Lemma lem514090 (m : nat) (n : nat) (p : nat) : (term13 m n p) = (term14 m n p).
Proof. exact (proj1 (@lem513551 n m p)). Qed.
Lemma lem514091 (m : nat) (n : nat) : (term15 m n) = (term16 m n).
Proof. exact (@lem514090 m m (Nat.add n n)). Qed.
Lemma lem514107 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem514108 (m : nat) (n : nat) : (term17 m n) = (term18 m n).
Proof. exact (MK_COMB (@lem514107) (@lem514091 m n)). Qed.
Lemma lem514110 (m : nat) (n : nat) (p : nat) : (term13 m n p) = (term14 m n p).
Proof. exact (proj1 (@lem513551 n m p)). Qed.
Lemma lem514111 (m : nat) (n : nat) : (term19 m n) = (term20 m n).
Proof. exact (@lem514110 m n (Nat.add m n)). Qed.
Lemma lem514119 (n : nat) (m : nat) (p : nat) : (term14 m n p) = (term14 n m p).
Proof. exact (proj2 (@lem513551 n m p)). Qed.
Lemma lem514120 (m : nat) (n : nat) : (term21 m n) = (term22 m n).
Proof. exact (@lem514119 m n n). Qed.
Lemma lem514130 (m : nat) : (Nat.add m) = (Nat.add m).
Proof. exact (eq_refl (Nat.add m)). Qed.
Lemma lem514131 (m : nat) (n : nat) : (term20 m n) = (term16 m n).
Proof. exact (MK_COMB (@lem514130 m) (@lem514120 m n)). Qed.
Lemma lem514138 (m : nat) (n : nat) : (term19 m n) = (term16 m n).
Proof. exact (TRANS (@lem514111 m n) (@lem514131 m n)). Qed.
Lemma lem514139 (m : nat) (n : nat) : ((term15 m n) = (term19 m n)) = ((term16 m n) = (term16 m n)).
Proof. exact (MK_COMB (@lem514108 m n) (@lem514138 m n)). Qed.
Lemma lem514141 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem514142 (x : nat) : (x = x) = True.
Proof. exact (@lem514141 nat x). Qed.
Lemma lem514143 (m : nat) (n : nat) : ((term16 m n) = (term16 m n)) = True.
Proof. exact (@lem514142 (term16 m n)). Qed.
Lemma lem514144 (m : nat) (n : nat) : ((term15 m n) = (term19 m n)) = True.
Proof. exact (TRANS (@lem514139 m n) (@lem514143 m n)). Qed.
Lemma lem514145 (m : nat) : (term23 m) = term1.
Proof. exact (fun_ext (fun n : nat => @lem514144 m n)). Qed.
Lemma lem514146 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem514147 (m : nat) : (term24 m) = term3.
Proof. exact (MK_COMB (@lem514146) (@lem514145 m)). Qed.
Lemma lem514149 {A : Type'} (t : Prop) : (term4 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem514150 (t : Prop) : (term5 t) = t.
Proof. exact (@lem514149 nat t). Qed.
Lemma lem514151 : term3 = True.
Proof. exact (@lem514150 True). Qed.
Lemma lem514152 (m : nat) : (term24 m) = True.
Proof. exact (TRANS (@lem514147 m) (@lem514151)). Qed.
Lemma lem514153 : term25 = term1.
Proof. exact (fun_ext (fun m : nat => @lem514152 m)). Qed.
Lemma lem514154 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem514155 : term26 = term3.
Proof. exact (MK_COMB (@lem514154) (@lem514153)). Qed.
Lemma lem514157 {A : Type'} (t : Prop) : (term4 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem514158 (t : Prop) : (term5 t) = t.
Proof. exact (@lem514157 nat t). Qed.
Lemma lem514159 : term3 = True.
Proof. exact (@lem514158 True). Qed.
Lemma lem514160 : term26 = True.
Proof. exact (TRANS (@lem514155) (@lem514159)). Qed.
Lemma lem514161 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem514162 : term27 = (and True).
Proof. exact (MK_COMB (@lem514161) (@lem514160)). Qed.
Lemma lem514164 (t : Prop) : (t /\ t) = t.
Proof. exact (proj2 (@lem1845 t)). Qed.
Lemma lem514165 : term28 = term26.
Proof. exact (@lem514164 term26). Qed.
Lemma lem514177 (m : nat) (n : nat) (p : nat) : (term13 m n p) = (term14 m n p).
Proof. exact (proj1 (@lem513551 n m p)). Qed.
Lemma lem514178 (m : nat) (n : nat) : (term15 m n) = (term16 m n).
Proof. exact (@lem514177 m m (Nat.add n n)). Qed.
Lemma lem514194 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem514195 (m : nat) (n : nat) : (term17 m n) = (term18 m n).
Proof. exact (MK_COMB (@lem514194) (@lem514178 m n)). Qed.
Lemma lem514197 (m : nat) (n : nat) (p : nat) : (term13 m n p) = (term14 m n p).
Proof. exact (proj1 (@lem513551 n m p)). Qed.
Lemma lem514198 (m : nat) (n : nat) : (term19 m n) = (term20 m n).
Proof. exact (@lem514197 m n (Nat.add m n)). Qed.
Lemma lem514206 (n : nat) (m : nat) (p : nat) : (term14 m n p) = (term14 n m p).
Proof. exact (proj2 (@lem513551 n m p)). Qed.
Lemma lem514207 (m : nat) (n : nat) : (term21 m n) = (term22 m n).
Proof. exact (@lem514206 m n n). Qed.
Lemma lem514217 (m : nat) : (Nat.add m) = (Nat.add m).
Proof. exact (eq_refl (Nat.add m)). Qed.
Lemma lem514218 (m : nat) (n : nat) : (term20 m n) = (term16 m n).
Proof. exact (MK_COMB (@lem514217 m) (@lem514207 m n)). Qed.
Lemma lem514225 (m : nat) (n : nat) : (term19 m n) = (term16 m n).
Proof. exact (TRANS (@lem514198 m n) (@lem514218 m n)). Qed.
Lemma lem514226 (m : nat) (n : nat) : ((term15 m n) = (term19 m n)) = ((term16 m n) = (term16 m n)).
Proof. exact (MK_COMB (@lem514195 m n) (@lem514225 m n)). Qed.
Lemma lem514228 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem514229 (x : nat) : (x = x) = True.
Proof. exact (@lem514228 nat x). Qed.
Lemma lem514230 (m : nat) (n : nat) : ((term16 m n) = (term16 m n)) = True.
Proof. exact (@lem514229 (term16 m n)). Qed.
Lemma lem514231 (m : nat) (n : nat) : ((term15 m n) = (term19 m n)) = True.
Proof. exact (TRANS (@lem514226 m n) (@lem514230 m n)). Qed.
Lemma lem514232 (m : nat) : (term23 m) = term1.
Proof. exact (fun_ext (fun n : nat => @lem514231 m n)). Qed.
Lemma lem514233 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem514234 (m : nat) : (term24 m) = term3.
Proof. exact (MK_COMB (@lem514233) (@lem514232 m)). Qed.
Lemma lem514236 {A : Type'} (t : Prop) : (term4 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem514237 (t : Prop) : (term5 t) = t.
Proof. exact (@lem514236 nat t). Qed.
Lemma lem514238 : term3 = True.
Proof. exact (@lem514237 True). Qed.
Lemma lem514239 (m : nat) : (term24 m) = True.
Proof. exact (TRANS (@lem514234 m) (@lem514238)). Qed.
Lemma lem514240 : term25 = term1.
Proof. exact (fun_ext (fun m : nat => @lem514239 m)). Qed.
Lemma lem514241 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem514242 : term26 = term3.
Proof. exact (MK_COMB (@lem514241) (@lem514240)). Qed.
Lemma lem514244 {A : Type'} (t : Prop) : (term4 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem514245 (t : Prop) : (term5 t) = t.
Proof. exact (@lem514244 nat t). Qed.
Lemma lem514246 : term3 = True.
Proof. exact (@lem514245 True). Qed.
Lemma lem514247 : term26 = True.
Proof. exact (TRANS (@lem514242) (@lem514246)). Qed.
Lemma lem514248 : term28 = True.
Proof. exact (TRANS (@lem514165) (@lem514247)). Qed.
Lemma lem514249 : term29 = (True /\ True).
Proof. exact (MK_COMB (@lem514162) (@lem514248)). Qed.
Lemma lem514251 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem514252 : (True /\ True) = True.
Proof. exact (@lem514251 True). Qed.
Lemma lem514253 : term29 = True.
Proof. exact (TRANS (@lem514249) (@lem514252)). Qed.
Lemma lem514254 : term30 = (True /\ True).
Proof. exact (MK_COMB (@lem514076) (@lem514253)). Qed.
Lemma lem514256 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem514257 : (True /\ True) = True.
Proof. exact (@lem514256 True). Qed.
Lemma lem514258 : term30 = True.
Proof. exact (TRANS (@lem514254) (@lem514257)). Qed.
Lemma lem514259 : term31 = (True /\ True).
Proof. exact (MK_COMB (@lem513990) (@lem514258)). Qed.
Lemma lem514261 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem514262 : (True /\ True) = True.
Proof. exact (@lem514261 True). Qed.
Lemma lem514263 : term31 = True.
Proof. exact (TRANS (@lem514259) (@lem514262)). Qed.
Lemma lem514264 : term32 = (True /\ True).
Proof. exact (MK_COMB (@lem513970) (@lem514263)). Qed.
Lemma lem514266 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem514267 : (True /\ True) = True.
Proof. exact (@lem514266 True). Qed.
Lemma lem514268 : term32 = True.
Proof. exact (TRANS (@lem514264) (@lem514267)). Qed.
Lemma lem514269 : term33 = (True /\ True).
Proof. exact (MK_COMB (@lem513950) (@lem514268)). Qed.
Lemma lem514271 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem514272 : (True /\ True) = True.
Proof. exact (@lem514271 True). Qed.
Lemma lem514273 : term33 = True.
Proof. exact (TRANS (@lem514269) (@lem514272)). Qed.
Lemma lem514274 : term34 = (True /\ True).
Proof. exact (MK_COMB (@lem513930) (@lem514273)). Qed.
Lemma lem514276 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem514277 : (True /\ True) = True.
Proof. exact (@lem514276 True). Qed.
Lemma lem514278 : term34 = True.
Proof. exact (TRANS (@lem514274) (@lem514277)). Qed.
Lemma lem514279 : term35 = (True /\ True).
Proof. exact (MK_COMB (@lem513910) (@lem514278)). Qed.
Lemma lem514281 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem514282 : (True /\ True) = True.
Proof. exact (@lem514281 True). Qed.
Lemma lem514283 : term35 = True.
Proof. exact (TRANS (@lem514279) (@lem514282)). Qed.
Lemma lem514284 : term36 = (True /\ True).
Proof. exact (MK_COMB (@lem513902) (@lem514283)). Qed.
Lemma lem514286 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem514287 : (True /\ True) = True.
Proof. exact (@lem514286 True). Qed.
Lemma lem514288 : term36 = True.
Proof. exact (TRANS (@lem514284) (@lem514287)). Qed.
Lemma lem514289 : True = term36.
Proof. exact (SYM (@lem514288)). Qed.
Lemma lem514290 : term36.
Proof. exact (EQ_MP (@lem514289) (@lem0)). Qed.
