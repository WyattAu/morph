"""
Link cache for link checker module.

This module implements a thread-safe cache for link validation results.
"""

import threading
from typing import Optional


class LinkCache:
    """Thread-safe cache for link validation results.

    This class provides a simple in-memory cache for storing
    link validation results to avoid redundant checks. The cache
    is thread-safe and can be used by multiple threads
    concurrently.

    The cache stores:
    - URL as key
    - Validation result (True/False) as value
    """

    def __init__(self) -> None:
        """Initialize the link cache."""
        self._cache: dict[str, bool] = {}
        self._lock = threading.Lock()

    def get(self, url: str) -> Optional[bool]:
        """Get cached validation result for a URL.

        Args:
            url: URL to look up in cache

        Returns:
            Cached validation result, or None if not in cache
        """
        with self._lock:
            return self._cache.get(url)

    def set(self, url: str, result: bool) -> None:
        """Cache validation result for a URL.

        Args:
            url: URL to cache
            result: Validation result (True if valid, False if invalid)
        """
        with self._lock:
            self._cache[url] = result

    def clear(self) -> None:
        """Clear all cached results."""
        with self._lock:
            self._cache.clear()

    def __len__(self) -> int:
        """Get the number of cached items.

        Returns:
            Number of items in cache
        """
        with self._lock:
            return len(self._cache)

    def __contains__(self, url: str) -> bool:
        """Check if URL is in cache.

        Args:
            url: URL to check

        Returns:
            True if URL is in cache, False otherwise
        """
        with self._lock:
            return url in self._cache
