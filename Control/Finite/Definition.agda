module Control.Finite.Definition where 
open import Num.Natural.Definition as ℕ using (ℕ)

data Fin : ℕ → Set where 
    fst : {n : ℕ} → Fin n
    nxt : {n : ℕ} → Fin n → Fin (ℕ.succ n) 

pattern ⑴ = fst 
pattern ⑵ = nxt ⑴
pattern ⑶ = nxt ⑵
pattern ⑷ = nxt ⑶
pattern ⑸ = nxt ⑷
pattern ⑹ = nxt ⑸
pattern ⑺ = nxt ⑹
pattern ⑻ = nxt ⑺
pattern ⑼ = nxt ⑻
pattern ⑽ = nxt ⑼
pattern ⑾ = nxt ⑽
pattern ⑿ = nxt ⑾
pattern ⒀ = nxt ⑿
pattern ⒁ = nxt ⒀
pattern ⒂ = nxt ⒁
pattern ⒃ = nxt ⒂
pattern ⒄ = nxt ⒃
pattern ⒅ = nxt ⒄
pattern ⒆ = nxt ⒅
pattern ⒇ = nxt ⒆
