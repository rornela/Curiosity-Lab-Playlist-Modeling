#lang forge
open "playlist.frg"

test expect {
  // Basic satisfiability tests
  modelNotVacuous: {
    wellformedElements
  } for 4 Song, 2 Artist, 2 Album, 2 Genre, 4 Int is sat
  
  playlistNotVacuous: {
    wellformedElements
    some p: Playlist | wellformedPlaylist[p]
  } for 1 Playlist, 4 Song, 2 Artist, 2 Album, 2 Genre, 4 Int is sat

  // Test that we can have a non-empty playlist
  nonEmptyPlaylist: {
    wellformedElements
    some p: Playlist | {
      wellformedPlaylist[p]
      some p.sequence[Int]
      p.lastIndex >= 0
    }
  } for 1 Playlist, 4 Song, 2 Artist, 2 Album, 2 Genre, 4 Int is sat

  // Test that negative play counts violate well-formedness
  negativePlayCountTest: {
    some s: Song | s.playCount < 0
    wellformedElements
  } for 4 Song, 2 Artist, 2 Album, 2 Genre, 4 Int is unsat

  // Test that artist must match album artist
  artistMismatchTest: {
    some s: Song | s.artist != s.album.albumArtist
    wellformedElements
  } for 4 Song, 2 Artist, 2 Album, 2 Genre, 4 Int is unsat

  // Test that playlist cannot have gaps
  playlistGapsTest: {
    some p: Playlist | {
      some i: Int | {
        i > 0
        some p.sequence[i]
        no p.sequence[subtract[i, 1]]
        wellformedPlaylist[p]
      }
    }
  } for 1 Playlist, 4 Song, 2 Artist, 2 Album, 2 Genre, 4 Int is unsat

  // Test that lastIndex matches the actual last index
  lastIndexTest: {
    some p: Playlist | {
      p.lastIndex = 2
      some p.sequence[0]
      some p.sequence[1]
      some p.sequence[2]
      no p.sequence[3]
      wellformedPlaylist[p]
    }
  } for 1 Playlist, 4 Song, 2 Artist, 2 Album, 2 Genre, 4 Int is sat

  // Test that noDuplicates functions correctly
  noDuplicatesTest: {
    wellformedElements
    some p: Playlist | {
      wellformedPlaylist[p]
      p.lastIndex >= 1
      p.sequence[0] = p.sequence[1]
      noDuplicates[p]
    }
  } for 1 Playlist, 4 Song, 2 Artist, 2 Album, 2 Genre, 4 Int is unsat

  // Test that noConsecutiveSameArtist functions correctly
  noConsecutiveSameArtistTest: {
    wellformedElements
    some p: Playlist, s1, s2: Song | {
      perceptuallyRandomShuffle[p]
      p.sequence[0] = s1
      p.sequence[1] = s2
      s1.artist = s2.artist
      noConsecutiveSameArtist[p]
    }
  } for 1 Playlist, 4 Song, 2 Artist, 2 Album, 2 Genre, 4 Int is unsat


  // Test that limitConsecutiveSameGenre doesn't allow 5 consecutive songs of same genre
  limitConsecutiveSameGenreForbidsTest: {
    wellformedElements
    some p: Playlist, g: Genre, s1, s2, s3, s4, s5: Song | {
      wellformedPlaylist[p]
      s1.genre = g and s2.genre = g and s3.genre = g and s4.genre = g and s5.genre = g
      p.sequence[0] = s1
      p.sequence[1] = s2
      p.sequence[2] = s3
      p.sequence[3] = s4
      p.sequence[4] = s5
      p.lastIndex = 4
      limitConsecutiveSameGenre[p]
    }
  } for 1 Playlist, 5 Song, 2 Artist, 2 Album, 1 Genre, 5 Int is unsat

  // Test smoothEnergyTransition functions correctly
  smoothEnergyTransitionTest: {
    wellformedElements
    some p: Playlist, s1, s2: Song | {
      wellformedPlaylist[p]
      p.sequence[0] = s1
      p.sequence[1] = s2
      p.lastIndex = 1
      s1.energy = 0
      s2.energy = 7  // Energy difference of 7, exceeds maxJump of 5
      smoothEnergyTransition[p, 5]
    }
  } for 1 Playlist, 4 Song, 2 Artist, 2 Album, 2 Genre, 4 Int is unsat

  // Test that spaceOutRecentlyPlayed works correctly
  spaceOutRecentlyPlayedTest: {
    wellformedElements
    some p: Playlist, s1, s2: Song | {
      wellformedPlaylist[p]
      p.sequence[0] = s1
      p.sequence[1] = s2
      p.lastIndex = 1
      s1.recentlyPlayed = 1
      s2.recentlyPlayed = -1
      spaceOutRecentlyPlayed[p]
    }
  } for 1 Playlist, 4 Song, 2 Artist, 2 Album, 2 Genre, 4 Int is unsat

  // Test that balancedExposure requires both popular and less-played songs
  balancedExposureTest: {
    wellformedElements
    some p: Playlist | {
      wellformedPlaylist[p]
      p.lastIndex >= 3
      all s: Song | s in p.sequence[Int] implies s.playCount <= 1  // All songs are less-played
      balancedExposure[p]
    }
  } for 1 Playlist, 4 Song, 2 Artist, 2 Album, 2 Genre, 4 Int is unsat

  // Test perceptuallyRandomShuffle is satisfiable
  perceptuallyRandomShuffleSat: {
    wellformedElements
    some p: Playlist | {
      perceptuallyRandomShuffle[p]
      p.lastIndex >= 3
    }
  } for 1 Playlist, 8 Song, 4 Artist, 4 Album, 4 Genre, 4 Int is sat

  // Test trulyRandomShuffle allows same-artist consecutive songs
  trulyRandomAllowsSameArtist: {
    wellformedElements
    some p: Playlist, a: Artist, s1, s2: Song | {
      wellformedPlaylist[p]
      p.sequence[0] = s1
      p.sequence[1] = s2
      p.lastIndex = 1
      s1.artist = a
      s2.artist = a
      trulyRandomShuffle[p]
    }
  } for 1 Playlist, 4 Song, 2 Artist, 2 Album, 2 Genre, 4 Int is sat

  // Test that perceptually random is more constrained than truly random
  perceptuallyRandomMoreConstrained: {
    wellformedElements
    some p: Playlist | {
      trulyRandomShuffle[p]
      not perceptuallyRandomShuffle[p]
      p.lastIndex >= 1
    }
  } for 1 Playlist, 4 Song, 2 Artist, 2 Album, 2 Genre, 4 Int is sat

  // Test that highest ID song can win
  userSatisfiedTest: {
    wellformedElements
    some p: Playlist | {
      userSatisfied[p]
      p.lastIndex >= 3
    }
  } for 1 Playlist, 8 Song, 4 Artist, 4 Album, 4 Genre, 4 Int is sat

  // Test that perceptuallyRandomShuffle implies all of its constituent constraints
  perceptualRandomImpliesNoDuplicates: {
    all p: Playlist | perceptuallyRandomShuffle[p] implies noDuplicates[p]
  } for 1 Playlist, 4 Song, 2 Artist, 2 Album, 2 Genre, 4 Int is checked

  perceptualRandomImpliesNoConsecutiveSameArtist: {
    all p: Playlist | perceptuallyRandomShuffle[p] implies noConsecutiveSameArtist[p]
  } for 1 Playlist, 4 Song, 2 Artist, 2 Album, 2 Genre, 4 Int is checked

  perceptualRandomImpliesSmoothEnergyTransition: {
    all p: Playlist | perceptuallyRandomShuffle[p] implies smoothEnergyTransition[p, 5]
  } for 1 Playlist, 4 Song, 2 Artist, 2 Album, 2 Genre, 4 Int is checked
}


