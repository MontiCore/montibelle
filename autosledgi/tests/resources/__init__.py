def get_resource(path: str):
    """
    Returns the location of the desired resource

    Args:
        path (str): a relative path (relative to the root resource directory)

    Returns:
        (str) an absolute path to the desired resource
    """
    import pathlib, os
    resource_dir = pathlib.Path(__file__).parent.resolve()
    return os.path.normpath(os.path.join(os.path.abspath(resource_dir), path))
