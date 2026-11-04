import logging
import os

import boto3
from botocore.client import ClientError

from autosledgi.cloudsledgi import logger
import autosledgi.cloudsledgi as c

"""
Documentation: https://boto3.amazonaws.com/v1/documentation/api/latest/reference/services/s3.html
"""

s3 = None


def init():
    if c.S3_ENDPOINT and c.S3_ACCESS_KEY and c.S3_SECRET_KEY:
        logger.info("Using custom credentials for s3.")
        set_custom_client(endpoint=c.S3_ENDPOINT, accesskey=c.S3_ACCESS_KEY, secretkey=c.S3_SECRET_KEY)
    else:
        logger.info("No custom configs configured. Trying to use AWS instead.")
        set_aws_client()


def set_aws_client():
    global s3
    s3 = boto3.resource("s3")
    s3.meta.client.head_bucket(Bucket=c.S3_BUCKET_NAME)


def set_custom_client(endpoint, accesskey, secretkey):
    global s3
    s3 = boto3.resource("s3", endpoint_url=endpoint, verify=True,
                        aws_access_key_id=accesskey, aws_secret_access_key=secretkey)

    s3.meta.client.head_bucket(Bucket=c.S3_BUCKET_NAME)


def __construct_obj_name(local_file_path, source):
    """
    Uses the localfilepath and the source folder to generate the object name for S3.
    """
    return os.path.normpath(local_file_path[len(source):])


def s3_put(source: str, prefix: str, bucket: str = c.S3_BUCKET_NAME, source_name_mapper=__construct_obj_name,
           exclude_extension=[]):
    """
    Uploads a directory to s3.
    """
    try:
        if not os.path.exists(source):
            logger.warning("Cannot upload not existing folder.")
            return False

        for root, _, files in os.walk(source):
            for file in files:
                if file.startswith("core."):
                    logger.debug(f"Skipping upload of {file}..")
                    continue

                def should_filter():
                    for extension in exclude_extension:
                        if file.endswith(extension):
                            return True
                    return False

                if should_filter():
                    continue

                local_path = os.path.normpath(os.path.join(root, file))

                obj_name = source_name_mapper(local_path, source)

                upload_path = os.path.normpath(
                    f"{prefix}/{obj_name}")

                logger.debug(
                    f"Uploading {local_path} >> {upload_path}")

                s3.Bucket(bucket).upload_file(local_path, upload_path)

        logger.info(f"All files from {source} uploaded.")
        return True
    except ClientError as ex:
        logger.warning(ex)
        logger.warning(
            f"Could not find or access specified bucket: {bucket}")
        return False


def s3_pull(prefix: str, target: str, delete_after_pull: bool = False, bucket=c.S3_BUCKET_NAME):
    """
    Downloads all files with a specific prefix.
    """
    logger.info(f'Fetching {prefix} from {bucket}..')
    try:
        s3.meta.client.head_bucket(Bucket=c.S3_BUCKET_NAME)
        bucket = s3.Bucket(c.S3_BUCKET_NAME)
        prefix_objs = bucket.objects.filter(Prefix=prefix)

        if len(list(prefix_objs)) == 0:
            logger.warning(
                f"There are no objects with prefix {prefix} or you are not allowed to access them.")
            return False

        for obj in prefix_objs:
            file_name = obj.key[len(prefix):]
            target = os.path.normpath(target)
            target_obj_path = os.path.normpath(os.path.join(target, file_name))
            logger.info(f'Downloading {file_name} >> {target_obj_path}..')
            if not os.path.exists(os.path.dirname(target_obj_path)):
                logger.debug(
                    f"Creating local folder {os.path.dirname(target_obj_path)}")
                os.makedirs(os.path.dirname(target_obj_path))

            bucket.download_file(obj.key, target_obj_path)

            if delete_after_pull:
                logger.debug(f'Deleting.. {obj}.')
                obj.delete()

        logger.info(f"Pulled {prefix} successfully!")
        return True

    except ClientError:
        logger.warning(f"Could not find or access files in bucket {bucket}.")
        return False


def s3_prefix_exists(prefix, bucket=c.S3_BUCKET_NAME):
    """
    Checks if there is at least one object with the specified prefix.
    """
    try:
        s3.meta.client.head_bucket(Bucket=bucket)
        bucket = s3.Bucket(bucket)
        result_objs = bucket.objects.filter(Prefix=prefix)

        return len(list(result_objs)) > 0
    except ClientError as ex:
        logging.warning(ex)
        return False


def s3_delete_prefix(prefix, bucket=c.S3_BUCKET_NAME):
    """
    Delete all objects with the specified prefix.
    """
    try:
        logger.info(f"Deleting prefix {prefix} from {bucket}..")
        s3.meta.client.head_bucket(Bucket=bucket)
        bucket = s3.Bucket(bucket)
        bucket.objects.filter(Prefix=prefix).delete()

        logger.info(f"Successfully deleted all objects with prefix {prefix}")
        return True
    except ClientError as ex:
        logger.warning(f"Error deleting prefix {prefix}")
        logger.warning(ex)
        return False
