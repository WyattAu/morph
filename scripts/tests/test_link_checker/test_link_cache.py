"""Tests for link_cache."""

from spec_tools.link_checker.cache.link_cache import LinkCache


class TestLinkCache:
    def test_init(self):
        cache = LinkCache()
        assert len(cache) == 0

    def test_get_miss(self):
        cache = LinkCache()
        assert cache.get("http://example.com") is None

    def test_set_and_get(self):
        cache = LinkCache()
        cache.set("http://example.com", True)
        assert cache.get("http://example.com") is True

    def test_contains(self):
        cache = LinkCache()
        assert "http://example.com" not in cache
        cache.set("http://example.com", False)
        assert "http://example.com" in cache

    def test_clear(self):
        cache = LinkCache()
        cache.set("a", True)
        cache.set("b", False)
        assert len(cache) == 2
        cache.clear()
        assert len(cache) == 0

    def test_overwrite(self):
        cache = LinkCache()
        cache.set("url", True)
        assert cache.get("url") is True
        cache.set("url", False)
        assert cache.get("url") is False

    def test_len(self):
        cache = LinkCache()
        assert len(cache) == 0
        cache.set("a", True)
        assert len(cache) == 1
        cache.set("b", False)
        assert len(cache) == 2
