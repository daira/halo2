window.BENCHMARK_DATA = {
  "lastUpdate": 1789833423394,
  "repoUrl": "https://github.com/daira/halo2",
  "entries": {
    "halo2 Benchmark": [
      {
        "commit": {
          "author": {
            "email": "kris@nutty.land",
            "name": "Kris Nuttycombe",
            "username": "nuttycom"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "79213cbe922e8868500e5944c407c69d893ec3a8",
          "message": "Merge pull request #936 from zcash/dw/msrv-1.88\n\nUse MSRV 1.88",
          "timestamp": "2026-09-09T10:16:58-06:00",
          "tree_id": "fa58dfa45549cc2e0e215b519a6d4024fea44ed1",
          "url": "https://github.com/daira/halo2/commit/79213cbe922e8868500e5944c407c69d893ec3a8"
        },
        "date": 1789833422646,
        "tool": "cargo",
        "benches": [
          {
            "name": "WIDTH = 3, RATE = 2-prover",
            "value": 73678320,
            "range": "± 3172563",
            "unit": "ns/iter"
          },
          {
            "name": "WIDTH = 3, RATE = 2-verifier",
            "value": 4041763,
            "range": "± 123253",
            "unit": "ns/iter"
          },
          {
            "name": "WIDTH = 9, RATE = 8-prover",
            "value": 138099102,
            "range": "± 3010883",
            "unit": "ns/iter"
          },
          {
            "name": "WIDTH = 9, RATE = 8-verifier",
            "value": 4562702,
            "range": "± 83884",
            "unit": "ns/iter"
          },
          {
            "name": "WIDTH = 12, RATE = 11-prover",
            "value": 189781867,
            "range": "± 2014352",
            "unit": "ns/iter"
          },
          {
            "name": "WIDTH = 12, RATE = 11-verifier",
            "value": 4747085,
            "range": "± 35781",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon/2-to-1",
            "value": 29678,
            "range": "± 198",
            "unit": "ns/iter"
          },
          {
            "name": "Sinsemilla/hash-to-point/510",
            "value": 116000,
            "range": "± 269",
            "unit": "ns/iter"
          },
          {
            "name": "Sinsemilla/hash/510",
            "value": 128589,
            "range": "± 426",
            "unit": "ns/iter"
          },
          {
            "name": "Sinsemilla/commit/510",
            "value": 216239,
            "range": "± 481",
            "unit": "ns/iter"
          },
          {
            "name": "Sinsemilla/short-commit/510",
            "value": 215944,
            "range": "± 417",
            "unit": "ns/iter"
          },
          {
            "name": "Sinsemilla/hash-to-point/520",
            "value": 118601,
            "range": "± 2586",
            "unit": "ns/iter"
          },
          {
            "name": "Sinsemilla/hash/520",
            "value": 130483,
            "range": "± 278",
            "unit": "ns/iter"
          },
          {
            "name": "Sinsemilla/commit/520",
            "value": 218499,
            "range": "± 1352",
            "unit": "ns/iter"
          },
          {
            "name": "Sinsemilla/short-commit/520",
            "value": 218331,
            "range": "± 524",
            "unit": "ns/iter"
          },
          {
            "name": "Sinsemilla/hash-to-point/1086",
            "value": 248423,
            "range": "± 1238",
            "unit": "ns/iter"
          },
          {
            "name": "Sinsemilla/hash/1086",
            "value": 259379,
            "range": "± 604",
            "unit": "ns/iter"
          },
          {
            "name": "Sinsemilla/commit/1086",
            "value": 346458,
            "range": "± 3321",
            "unit": "ns/iter"
          },
          {
            "name": "Sinsemilla/short-commit/1086",
            "value": 347096,
            "range": "± 1152",
            "unit": "ns/iter"
          }
        ]
      }
    ]
  }
}