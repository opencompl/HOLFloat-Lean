import HOLFloat.Common
import HOLFloat.Fixed
import HOLFloat.Float

--NOTE: 
-- Why formal semantics? 
--   It's useful to show the correctness of e.g. peephole rewrites on floating points
--   Giving formal semantics would gives formal reasoning on models that uses real numbers, easier to reason about rounding errors
-- How do we know that `noncomputable` does not affect our output?
--   Even if we have `noncomputable` stuffs, the point of the definitions are giving a formal reasoning 
--   to our rewrites.
-- Does `num` in the upstream repo means Naturals or just integers?

--TODO:
-- Mathlibify all the stuffs
-- Add & prove major theorems
