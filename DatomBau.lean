-- Root of the `DatomBau` library: a verified Datomic core.
-- The append-only transaction log is ground truth; indexes and queries
-- are proven projections of it. Modules land phase by phase.

import DatomBau.Core
import DatomBau.Schema
import DatomBau.Spec
import DatomBau.Transactor
